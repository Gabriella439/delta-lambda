module Main( main ) where

{- TODO:
  profiling
  write tests
-}


--import           Paths_Delta-Lambda (version)
import           Data.Char                   (isSpace, isNumber)
import           System.FilePath             hiding ((</>))
import           Control.Applicative
import           Control.Monad.Except
import           Control.Monad.Reader
import           Control.Parallel
import           Data.ByteString             (writeFile, readFile)
import           Data.Text                   (Text, pack, unpack, length)
import           Data.Text.Encoding
import           Data.Text.IO
import           Data.Version
import           Data.Word                   (Word64)
import           GHC.Generics
import           Prelude                     hiding (getContents, putStrLn)
import           System.IO                   (Handle, IOMode (ReadMode, ReadWriteMode), withFile)

import           Text.Megaparsec             hiding (space)
import qualified Text.Megaparsec.Lexer       as Lexer
import           Text.Megaparsec.Text

import           Options

import           Text.PrettyPrint.Leijen     hiding ((<$>))

import           Language.Preprocessor.Cpphs

import           System.Console.Haskeline

import           Data.Serialize

-- represent a term with variable name type v, and variable binding index type i
-- that has metadata m associated to each node and leaf
data Term m v i = Variable v i m
                | Abstraction v m (Term m v i) (Term m v i)
                | Application m (Term m v i) (Term m v i)
                | Type m
                deriving (Generic)

data Kind m v i = Function v m (Term m v i) (Kind m v i)
                | Kind m
                deriving (Generic)

data DecompiledFileHeader = DecompiledFileHeader
  { compiledFileName   :: Text
  , interpreterVersion :: Version
  , extensionsUsed     :: [Text]
  }

data DecompiledFile m v i = DecompiledFile
  { decompiledFileHeader :: DecompiledFileHeader
  , decompiledTerm       :: Term m v i
  }

instance (Serialize m, Serialize v, Serialize i) => Serialize (Term m v i) where

instance (Serialize m, Serialize v, Serialize i) => Serialize (Kind m v i) where

  -- some orphan instances
instance Serialize Version where
  put = \vers -> putListOf (put :: Putter Int) (versionBranch vers)
  get = do
    branchList :: [Int] <- getListOf get
    return Version { versionBranch = branchList
                   , versionTags = []
                   }

instance Serialize Text where
  put = \text' -> do
    putWord64le (fromIntegral (Data.Text.length text') :: Word64)
    put (encodeUtf8 text')
  get = do
    leng <- getWord64le
    bs <- getByteString (fromIntegral leng :: Int)
    return (decodeUtf8 bs)

instance Serialize SourcePos where
  put = \srcPos -> do
    put (sourceName srcPos)
    put (sourceLine srcPos)
    put (sourceColumn srcPos)
  get = do str :: String <- get
           pos1 :: Pos <- get
           pos2 :: Pos <- get
           return $ SourcePos str pos1 pos2

instance Serialize Pos where
  put = \pos -> putWord64le (fromIntegral (unPos pos) :: Word64)
  get = getWord64le >>= return . unsafePos . fromIntegral

instance Serialize DecompiledFileHeader where
  put = \decompHeader -> do
    put (compiledFileName decompHeader)
    put (interpreterVersion decompHeader)
    put (extensionsUsed decompHeader)
  get = do
    fname :: Text <- get
    iversion :: Version <- get
    xtensions :: [Text] <- get
    return DecompiledFileHeader
      { compiledFileName = fname
      , interpreterVersion = iversion
      , extensionsUsed = xtensions
      }

instance (Serialize m, Serialize v, Serialize i) => Serialize (DecompiledFile m v i) where
  put = \decomp -> do
    put (decompiledFileHeader decomp)
    put (decompiledTerm decomp)
  get = do
    fileHeader :: DecompiledFileHeader <- get
    fileBody :: Term m v i <- get
    return DecompiledFile
      { decompiledFileHeader = fileHeader
      , decompiledTerm = fileBody
      }

transpile :: (m -> m') -> (v -> v') -> (i -> i') -> DecompiledFile m v i -> DecompiledFile m' v' i'
transpile fm fv fi decompFile@DecompiledFile{ decompiledTerm = fileBody } =
  let transpile' t = case t of
                    Type m -> Type (fm m)
                    Variable v i m -> Variable (fv v) (fi i) (fm m)
                    Application m a f ->
                      Application (fm m) (transpile' a) (transpile' f)
                    Abstraction v m t b ->
                      Abstraction (fv v) (fm m) (transpile' t) (transpile' b)
  in decompFile { decompiledTerm = transpile' fileBody }





bindTerm :: (Eq v, Eq i, Enum i) => v -> i -> Term m v i -> Term m v i
bindTerm variable index subject = case subject of
  Type metadata -> Type metadata
  Application metadata argument function ->
    Application metadata (bindTerm variable index argument) (bindTerm variable index function)
  Abstraction variable' metadata parameter body ->
    Abstraction variable' metadata (bindTerm variable index parameter)
                                  (bindTerm variable (succ index) body)
  Variable variable' index' metadata
    | variable == variable' && index' == toEnum 0 -> Variable variable' index metadata
    | otherwise -> subject

bindContext :: (Eq i, Enum i, Show i) => [Term m Text i] -> i -> Term m Text i -> Term m Text i
bindContext context index term = case context of
  [] -> term
  _:rest -> bindContext rest (succ index) (bindTerm (pack ("$" ++ show index)) index term)

updateTerm :: (Ord i, Enum i) => i -> i -> Term m v i -> Term m v i
updateTerm i k subject = case subject of
  Type metadata -> Type metadata
  Application metadata argument function ->
    Application metadata (updateTerm i k argument) (updateTerm i k function)
  Abstraction variable metadata parameter body ->
    Abstraction variable metadata (updateTerm i k parameter) (updateTerm i (succ k) body)
  Variable variable index metadata
    | index > k -> Variable variable (toEnum $ fromEnum index + fromEnum i - 1) metadata
    | otherwise -> subject

substituteTerm :: (Ord i, Enum i) => i -> Term m v i -> Term m v i -> Term m v i
substituteTerm index replacement' subject =
  case subject of
    Type metadata -> Type metadata
    Application metadata argument function ->
      Application metadata (substituteTerm index replacement' argument)
      (substituteTerm index replacement' function)
    Abstraction variable metadata parameter body ->
      Abstraction variable metadata (substituteTerm index replacement' parameter)
      (substituteTerm (succ index) replacement' body)
    Variable variable index' metadata
      | index' >  index -> Variable variable (pred index') metadata
      | index' == index -> updateTerm index (toEnum 0) replacement'
      | index' <  index -> subject

substituteKind :: (Ord i, Enum i) => i -> Term m v i -> Kind m v i -> Kind m v i
substituteKind index replacement' subject = case subject of
  Kind metadata -> Kind metadata
  Function variable metadata parameter body ->
    Function variable metadata (substituteTerm index replacement' parameter)
                                           (substituteKind (succ index) replacement' body)

whnf :: (Ord i, Enum i) => Term m v i -> Term m v i
whnf reduct =
  case reduct of
    Application metadata argument function ->
      case whnf function of
        Abstraction _ _ _ body ->
          whnf $ substituteTerm (toEnum 1) argument body
        f@_ -> Application metadata argument f
    reduct'@_ -> reduct'

nfTerm :: (Enum i, Ord i) => Term m v i -> Term m v i
nfTerm reduct =
  case reduct of
    Abstraction variable metadata parameter body ->
      let parameter' = nfTerm parameter
          body' = parameter' `par` nfTerm body
      in Abstraction variable metadata parameter' body'
    Application metadata argument function ->
      case whnf function of
        Abstraction _ _ _ body ->
          let arg = nfTerm argument
              bod = arg `seq` substituteTerm (toEnum 1) arg (nfTerm body)
          in nfTerm bod
        f@_ -> Application metadata (nfTerm argument) (nfTerm f)
    _ -> reduct

nfKind :: (Enum i, Ord i) => Kind m v i -> Kind m v i
nfKind reduct =
  case reduct of
    Kind metadata -> Kind metadata
    Function variable metadata parameter body ->
      let param = nfTerm parameter
          body' = param `par` nfKind body
      in Function variable metadata param body'

instance (Enum i, Ord i, Eq v) => Eq (Term m v i) where
  Type _ == Type _ = True
  Variable variable index _ == Variable variable' index' _ = variable == variable' && index == index'
  Application _ argument function == Application _ argument' function' =
    let ftest = function == function'
        atest = ftest `par` argument == argument'
    in ftest && atest
  Abstraction variable metadata parameter body == Abstraction _ _ parameter' body' =
    let ptest = parameter == parameter'
        var   = Variable variable (toEnum 1) metadata
        btest = ptest `par` body == substituteTerm (toEnum 1) var body'
    in ptest && btest
  _ == _ = False

instance (Enum i, Ord i, Eq v, Eq i) => Eq (Kind m v i) where
  Kind _ == Kind _ = True
  Function variable metadata parameter body == Function _ _ parameter' body' =
    let ptest = parameter == parameter'
        var   = Variable variable (toEnum 1) metadata
        btest = ptest `par` body == substituteKind (toEnum 1) var body'
    in ptest && btest
  _ == _ = False

infix 4 ===
class (Enum i, Ord i, Eq i, Eq v) => BetaEq t v i where
  (===) :: (Enum i, Ord i, Eq i, Eq v) => t v i -> t v i -> Bool

instance (Enum i, Ord i, Eq i, Eq v) => BetaEq (Term m) v i where
  a === b = nfTerm a == nfTerm b

instance (Enum i, Ord i, Eq i, Eq v) => BetaEq (Kind m) v i where
  a === b = nfKind a == nfKind b

instance (Enum i, Ord i, Eq i, Eq v) => BetaEq (PseudoTerm m) v i where
  Term a === Term b = nfTerm a == nfTerm b
  Kind' a === Kind' b = nfKind a == nfKind b
  _ === _ = False




data PseudoTerm m v i = Term (Term m v i)
                    | Kind' (Kind m v i)

type Context m v i = [Term m v i]

type Judgement m v i a = ReaderT (Context m v i) (Either String) a

typeSynth :: (Show v, Enum i) => Term SourcePos v i -> Judgement SourcePos v i (PseudoTerm SourcePos v i)
typeSynth term' =
  case term' of
    Type metadata -> return $ Kind' (Kind metadata)
    Variable variable index position -> do
      context <- ask
      if Prelude.length context <= fromEnum index - 1 then
        throwError $ "invalid variable encountered during type synthesis: "
          ++ show variable ++ "\nat " ++ show position
        else return $ Term $ context !! (fromEnum index - 1)
    Application position argument function -> do
      function' <- typeSynth function
      case function' of
        Term f -> return $ Term $ Application position argument f
        Kind' _ -> throwError $ "invalid kind constructed during type synthesis"
          ++ "\nat "  ++ show position
    Abstraction variable position parameter body -> do
      body' <- local (parameter:) (typeSynth body)
      case body' of
        Term b -> return $ Term $ Abstraction variable position parameter b
        Kind' b -> return $ Kind' $ Function variable position parameter b

fTypeSynth :: (Show v, Enum i) => Term SourcePos v i -> Judgement SourcePos v i (PseudoTerm SourcePos v i)
fTypeSynth t = do
  typ <- typeSynth t
  case typ of
    Term t' -> fTypeSynth t'
    Kind' _ -> return typ

termCorrect :: (Enum i, Show v, BetaEq (PseudoTerm SourcePos) v i) => Term SourcePos v i -> Judgement SourcePos v i ()
termCorrect t = case t of
  Type _ -> return ()
  Variable{} ->
    void (typeSynth t)
  Abstraction _ _ parameter body -> do
    termCorrect parameter
    local (parameter:) (termCorrect body)
  Application pos argument function -> do
    argType <- typeSynth argument
    termCorrect argument
    Term funType <- fTypeSynth function
    case nfTerm funType of
      Abstraction _ _ parameter body ->
        if Term parameter === argType then
          termCorrect (nfTerm $ substituteTerm (toEnum 1) argument body)
        else
          let argPosition = show $ getNodeMetadata (Term argument)
              parPosition = show $ getNodeMetadata (Term parameter)
          in throwError $ "argument type and function parameter do not match: \n"
                ++ "at " ++ argPosition ++ " with argument type of:   " ++ show argType ++ "\n"
                ++ "at " ++ parPosition ++ " with parameter value of: " ++ show parameter ++ "\n"
      e@_ -> throwError $ "attempted application onto non function type at "
                ++ show pos ++ "\nwith type: " ++ show e





lineComment, blockComment, spaceToken :: Parser ()
lineComment = Lexer.skipLineComment "--" <|> Lexer.skipLineComment "#"
blockComment = Lexer.skipBlockComment "{-" "-}"
spaceToken = Lexer.space (void spaceChar) lineComment blockComment

lexeme :: Parser a -> Parser a
lexeme = Lexer.lexeme spaceToken

symbol :: String -> Parser String
symbol = Lexer.symbol spaceToken

variableToken :: Parser Text
variableToken = lexeme =<<
  return . pack <$> ((:) <$> (letterChar <|> Text.Megaparsec.char '$') <*> many alphaNumChar)

commaToken, colonToken, typeToken :: Parser ()
commaToken = void (symbol ",")
colonToken = void (symbol ":")
typeToken  = void (symbol "type")

parensToken, bracketsToken :: Parser a -> Parser a
parensToken   = between (symbol "(") (symbol ")")
bracketsToken = between (symbol "[") (symbol "]")

vector :: Parser [Term SourcePos Text Word64]
vector = sepBy1 term commaToken

telescope :: Parser [([(Text, SourcePos)], Term SourcePos Text Word64)]
telescope = sepBy1 ((,) <$> sepBy ((,) <$> variableToken <*> getPosition) spaceToken <*> (colonToken >> term)) commaToken

term :: Parser (Term SourcePos Text Word64)
term =   (Type <$> (typeToken >> getPosition) <?> "type")
     <|> try (Variable <$> variableToken <*> return 0 <*> getPosition <?> "variable")
     <|> (apply <$> parensToken vector <*> term <?> "application")
     <|> (funct <$> bracketsToken telescope <*> term <?> "abstraction")

apply :: [Term SourcePos v i] -> Term SourcePos v i -> Term SourcePos v i
apply = flip $ foldl (\f a -> Application (getNodeMetadata (Term a)) a f)

funct :: [([(Text, SourcePos)], Term SourcePos Text Word64)] -> Term SourcePos Text Word64 -> Term SourcePos Text Word64
funct = flip $ foldr $ \(ns, typ) bod -> foldr (\(n, p) -> Abstraction n p typ . bindTerm n 1) bod ns

parseString :: String -> Text -> Either String (Term SourcePos Text Word64)
parseString filename' input = case parse term filename' input of
  Left err -> Left $ show err
  Right val -> Right val

parseInput :: Text -> Either String (Term SourcePos Text Word64)
parseInput = parseString "stdin"





getNodeMetadata :: PseudoTerm m v i -> m
getNodeMetadata node = case node of
  Term term' -> case term' of
    Type metadata -> metadata
    Variable _ _ metadata -> metadata
    Abstraction _ metadata _ _ -> metadata
    Application metadata _ _ -> metadata
  Kind' kind -> case kind of
    Kind metadata -> metadata
    Function _ metadata _ _ -> metadata

prettyKind :: Show v => Kind m v i -> Doc
prettyKind kind = case kind of
  Kind _ -> text "kind"
  Function variable _ parameter body ->
    let (args, bod) = collectAbstr [(variable, parameter)] body
        argsDoc = list $ fmap (\(n, t) -> text (show n) <> colon <+> prettyTerm t) args
        funDoc = argsDoc `par` prettyKind bod

        collectAbstr args' (Function v _ t b) = collectAbstr (args' ++ [(v, t)]) b
        collectAbstr args' fun = (args', fun)
    in argsDoc </> funDoc

prettyTerm :: Show v => Term m v i -> Doc
prettyTerm term' = case term' of
  Type _ -> text "type"
  Variable variable _ _ -> text $ show variable
  Application _ arg fun ->
    let (args, fun') = collectApply [arg] fun
        argsDoc = tupled $ map prettyTerm args
        funDoc = argsDoc `par` prettyTerm fun'

        collectApply args' (Application _ arg' fun'') = collectApply (args' ++ [arg']) fun''
        collectApply args' fun'' = (args', fun'')
    in argsDoc </> funDoc
  Abstraction var _ typ bod ->
    let (args, bod') = collectAbstr [(var, typ)] bod
        argsDoc = list $ fmap (\(n, t) -> text (show n) <> colon <+> prettyTerm t) args
        funDoc = argsDoc `par` prettyTerm bod'

        collectAbstr args' (Abstraction v _ t b) = collectAbstr (args' ++ [(v, t)]) b
        collectAbstr args' fun = (args', fun)
    in argsDoc </> funDoc

instance Show v => Show (Term m v i) where
  showsPrec _ term' = displayS $ renderPretty 0.4 100 $ prettyTerm term'

instance Show v => Show (Kind m v i) where
  showsPrec _ kind = displayS $ renderPretty 0.4 100 $ prettyKind kind

instance (Show v) => Show (PseudoTerm m v i) where
  show p = case p of
    Term t -> show t
    Kind' k -> show k



data ReplOptions = ReplOptions
  { interactive  :: Bool
  , writeHistory :: Bool
  , historyFileN :: String
  , noHelpPrompt :: Bool
  }

data FileOptions = FileOptions
  { usePreprocessor     :: Bool
  , compileToByteCode   :: Bool
  , saveMetadata        :: Bool
  , preprocessorOptions :: [String]
  }

data MainOptions = MainOptions
  { inFile              :: String
  , echoType            :: Bool
  , useExtension        :: [String]
  , replOptions         :: ReplOptions
  , fileOptions         :: FileOptions
  }

fileGroup :: Maybe Group
fileGroup = Just $ Options.group "file" "file commands" "commands that only affect files"

replGroup :: Maybe Group
replGroup = Just $ Options.group "repl" "repl commands" "commands that only affect the repl"

fileAndReplGroup :: Maybe Group
fileAndReplGroup = Just $ Options.group "file-and-repl" "file and repl commands"
  "commands that both the file compiler and the repl interpreter share"

instance Options ReplOptions where
  defineOptions = pure ReplOptions
    <*> defineOption optionType_bool (\o -> o
          { optionLongFlags = ["interactive"]
          , optionDefault = False
          , optionShortFlags = ['n']
          , optionDescription = "start repl"
          , optionGroup = replGroup
          })
    
    <*> defineOption optionType_bool (\o -> o
          { optionLongFlags = ["write-history"]
          , optionDefault = True
          , optionShortFlags = ['w']
          , optionDescription = "enable writing to the history file"
          , optionGroup = replGroup
          })
    
    <*> defineOption optionType_string (\o -> o
          { optionLongFlags = ["history-file"]
          , optionDefault = "~/.delta-lambda"
          , optionShortFlags = ['f']
          , optionDescription = "set the history file name and location"
          , optionGroup = replGroup
          })

    <*> defineOption optionType_bool (\o -> o
          { optionLongFlags = ["no-help-prompt"]
          , optionDefault = False
          , optionShortFlags = ['k']
          , optionDescription = "dont issue help prompt on initial repl load"
          , optionGroup = replGroup
          })

instance Options FileOptions where
  defineOptions = pure FileOptions
    <*> defineOption optionType_bool (\o -> o
          { optionLongFlags = ["use-preprocessor"]
          , optionDefault = True
          , optionShortFlags = ['p']
          , optionDescription = "enable the preprocessor"
          , optionGroup = fileGroup
          })
    <*> defineOption optionType_bool (\o -> o
          { optionLongFlags = ["compile"]
          , optionDefault = False
          , optionShortFlags = ['o']
          , optionDescription = "enable compilation to bytecode"
          , optionGroup = fileGroup
          })
    <*> defineOption optionType_bool (\o -> o
          { optionLongFlags = ["without-metadata"]
          , optionDefault = False
          , optionShortFlags = ['s']
          , optionDescription = "save metadata during compilation to bytecode"
          , optionGroup = fileGroup
          })
    <*> defineOption (optionType_list ',' optionType_string) (\o -> o
          { optionLongFlags = ["preprocessor-flags"]
          , optionDefault = []
          , optionShortFlags = ['c']
          , optionDescription = "passes the proceeding flags to the preprocessor"
          , optionGroup = fileGroup
          })

instance Options MainOptions where
  defineOptions = pure MainOptions
    <*> defineOption optionType_string (\o -> o
          { optionLongFlags = ["in-file"]
          , optionDefault = "stdin"
          , optionShortFlags = ['i']
          , optionDescription =
              "input file usable extension must be one of "
              ++ "(*.dl, *.cdl). note that if the \"-n\""
              ++ " or \"--interactive\" flags are not used"
              ++ " in combination with this option, the compiler"
              ++ " will not load the file."
          , optionGroup = fileAndReplGroup
          })
    <*> defineOption optionType_bool (\o -> o
          { optionLongFlags = ["echo-type"]
          , optionDefault = True
          , optionShortFlags = ['e']
          , optionDescription = "enable echoing the type of a term after checking"
          , optionGroup = fileAndReplGroup
          })
    <*> defineOption (optionType_list ',' optionType_string) (\o -> o
          { optionLongFlags = ["use-extensions"]
          , optionDefault = []
          , optionShortFlags = ['x']
          , optionDescription =
              "enables a set of extensions"
          , optionGroup = fileAndReplGroup
          })
    <*> defineOptions
    <*> defineOptions
    
version :: Version
version = Version
  { versionBranch = [0,1,0,0]
  , versionTags = [] -- depreciated, but showVersion throws an exception without it
  }

replPrompt :: Version -> String
replPrompt vers = Prelude.unlines
  [ "    /\\         /\\"
  , "   /  \\       /  \\"
  , "  / /\\ \\     / /\\ \\"
  , " / /__\\ \\   / /  \\ \\"
  , "/________\\ /_/    \\_\\"
  , "Welcome to Delta-Lambda, the 1000 line[s of haskell] theorem prover!"
  , "This is apha level software! no documentation currently, and dragons galore!"
  , "version: " ++ showVersion vers
  ]

helpPrompt :: String
helpPrompt = Prelude.unlines
  [ "/-----------------------------------------------------------------------------\\"
  , "| command | parameters | description                                          |"
  , "| :c      | input term | check that the input term is correct                 |"
  , "| :e      | posn, term | add a term to the context at the position            |"
  , "| :f      | input term | provide the final type of the input term             |"
  , "| :g      | position   | get the type of a term name (or position) in context |"
  , "| :h      |            | display this table                                   |"
  , "| :o      | file name  | open a file and load it                              |"
  , "| :q      |            | quit this repl                                       |"
  , "| :r      | input term | provide the normal form of the input term            |"
  , "| :t      | input term | provide the type of the input term                   |"
  , "| :s      | input flag | set a flag, restart the repl                         |"
  , "| :?      |            | syntax and semantics tutorial (not implemented)      |"
  , "\\-----------------------------------------------------------------------------/"
  ]

data ReplState = ReplState
  { replContext :: Context SourcePos Text Word64
  , replTerm    :: Maybe (Term SourcePos Text Word64)
  , replOpts    :: MainOptions
  }

main :: IO ()
main = runCommand $ \opts _ ->
  if interactive $ replOptions opts then
    repl opts
  else
    if takeExtension (inFile opts) == ".dl" then
      withFile (inFile opts) ReadMode $ parseCheckAndType opts
    else
      if takeExtension (inFile opts) == ".cdl" then
        putStrLn . pack $ "cannot open binary file in non interactive mode!"
      else
        putStrLn . pack $ "extension not recognized: " ++ takeExtension (inFile opts)

preprocess :: MainOptions -> Text -> IO (Either String Text)
preprocess options fileContents =
  if usePreprocessor $ fileOptions options then
    case Language.Preprocessor.Cpphs.parseOptions (preprocessorOptions $ fileOptions options) of
      Left err -> return $ Left err
      Right cpphsOpts -> do
        fileContents' <- runCpphs cpphsOpts (inFile options) (unpack fileContents)
        return $ Right $ pack fileContents'
  else return $ Right fileContents

compile :: (Serialize m , Serialize v, Serialize i) => Term m v i -> MainOptions -> IO ()
compile val options
  | not (saveMetadata $ fileOptions options) = Data.ByteString.writeFile compiledFilename (encode file)
  | otherwise =  Data.ByteString.writeFile compiledFilename (encode cleaned)
  where header = DecompiledFileHeader
          { compiledFileName = pack $ inFile options
          , interpreterVersion = version
          , extensionsUsed = map pack $ useExtension options
          }
        
        file = DecompiledFile
          { decompiledFileHeader = header
          , decompiledTerm = val
          }

        cleaned = transpile (const ()) id id file
        
        compiledFilename = dropExtension (inFile options) -<.> ".cdl"
      

checkAndType :: (Enum i, Show v, BetaEq (PseudoTerm SourcePos) v i) => Term SourcePos v i -> MainOptions -> Context SourcePos v i -> IO (Maybe ())
checkAndType term options context =
  case runReaderT (termCorrect term) context of
    Left err -> do
      putStrLn $ pack err
      return Nothing
    Right _
      | echoType options ->
        case runReaderT (typeSynth term) context of
          Left err -> do
            putStrLn $ pack err
            return Nothing
          Right val -> do
            putStrLn . pack $ show val
            return $ Just ()
      | otherwise -> do
          return $ Just ()

parseCheckAndType :: MainOptions -> Handle -> IO ()
parseCheckAndType options file = do
  input <- Data.Text.IO.hGetContents file
  input' <- preprocess options input
  case input' of
    Left pperr -> putStrLn $ pack pperr
    Right ppval ->
      case parseInput ppval of
        Left perr -> putStrLn $ pack perr
        Right pval -> do
          checked <- checkAndType pval options []
          case checked of
            Nothing -> return ()
            Just _ -> 
              if compileToByteCode $ fileOptions options then
                compile pval options
              else
                return ()

repl :: MainOptions -> IO ()
repl options = do
  Data.Text.IO.putStr $ pack (replPrompt version)
  when (not (noHelpPrompt (replOptions options))) $ Data.Text.IO.putStr (pack helpPrompt)
  if inFile options == "stdin" then
    runInputT replSettings $ loop (initReplState Nothing options)
    else
    if takeExtension (inFile options) == ".dl" then do
      withFile (inFile options) ReadWriteMode $ \h -> do
        input <- Data.Text.IO.hGetContents h
        input' <- preprocess options input
        case input' of
          Left pperr -> putStrLn $ pack pperr
          Right ppval ->
            case parseInput ppval of
              Left perr -> putStrLn $ pack perr
              Right pval -> do
                checked <- checkAndType pval options []
                case checked of
                  Nothing -> return ()
                  Just _ -> runInputT replSettings $ loop (initReplState (Just pval) options)
    else
      if takeExtension (inFile options) == ".cdl" then do
        fileCont <- Data.ByteString.readFile (inFile options)
        case decode fileCont :: Either String (DecompiledFile SourcePos Text Word64) of
          Left perr -> putStrLn $ pack perr
          Right pval -> do
            let fvers = interpreterVersion (decompiledFileHeader pval)
            if fvers < version then
              putStrLn . pack $ "cannot load file \"" ++ inFile options ++ "\n" ++
              "compiler version of file:   " ++ showVersion fvers ++ "\n" ++
              "compiler version of system: " ++ showVersion version
              else do
                let val = decompiledTerm pval
                runInputT replSettings $ loop (initReplState (Just val) options)
      else
        putStrLn . pack $ "extension not recognized: " ++ takeExtension (inFile options)
              
  where replSettings = defaultSettings
          { historyFile = Just $ historyFileN (replOptions options)
          , autoAddHistory = writeHistory (replOptions options)
          }

initReplState term options = ReplState
  { replContext = []
  , replTerm = term
  , replOpts = options
  }

loop :: ReplState -> InputT IO ()
loop state = do
  let count = Prelude.length (replContext state)
  input <- getInputLine $ if count == 0 then "|- " else show count ++ " |- "
  case input of
    Nothing -> loop state
    Just (':':'c':' ':rest) -> do
      case parseInput (pack rest) of
        Left perr -> do
          outputStrLn perr
          loop state
        Right pval -> do
          lift $ checkAndType pval (replOpts state) (replContext state)
          loop state
    Just (':':'e':' ':rest) -> do
      let positionStr = takeWhile (\x -> not (isSpace x) && isNumber x) rest
      let termStr = dropWhile (\x -> not (isSpace x) && isNumber x) rest
      if null positionStr then do
        outputStrLn "please enter a non-negative number"
        loop state
        else do
          let position :: Int = read positionStr
          case parseInput $ pack termStr of
            Left perr -> do
              outputStrLn perr
              loop state
            Right pval -> do
              checked <- lift $ checkAndType pval (replOpts state) (replContext state)
              case checked of
                Nothing -> loop state
                Just _ -> do
                  let (before, after) = splitAt position (replContext state)
                  let pval' = bindContext (replContext state) 1 pval
                  loop (state { replContext = before ++ [pval'] ++ after })
              
    Just (':':'f':' ':rest) ->
      case parseInput (pack rest) of
        Left perr -> do
          outputStrLn perr
          loop state
        Right pval -> do
          checked <- lift $ checkAndType pval (replOpts state) (replContext state)
          case checked of
            Nothing -> loop state
            Just _ ->
              case runReaderT (fTypeSynth pval) (replContext state) of
                Left err -> do
                  outputStrLn err
                  loop state
                Right val -> do
                  outputStrLn $ show val
                  loop state
    Just (':':'g':' ':rest) -> do
      let positionStr = takeWhile (\x -> not (isSpace x) && isNumber x) rest
      if null positionStr then do
        outputStrLn "please enter a non-negative number"
        loop state
        else do
          let position :: Int = read positionStr
          if position > Prelude.length (replContext state) then do
            outputStrLn "position of term in context cannot be outside of context"
            loop state
            else do
            let term = (replContext state) !! (position - 1)
            outputStrLn $ show term
            loop state
    Just (':':'h':       _) -> do
      outputStrLn helpPrompt
      loop state
    Just (':':'o':' ':rest) -> do
      if takeExtension rest == ".dl" then do
        loaded <- lift $ withFile rest ReadWriteMode $ \h -> do
          input <- Data.Text.IO.hGetContents h
          input' <- preprocess (replOpts state) input
          case input' of
            Left pperr -> do
              putStrLn $ pack pperr
              return Nothing
            Right ppval ->
              case parseInput ppval of
                Left perr -> do
                  putStrLn $ pack perr
                  return Nothing
                Right pval -> do
                  checked <- checkAndType pval (replOpts state) []
                  case checked of
                    Nothing -> return Nothing
                    Just _ -> return $ Just pval
        case loaded of
          Nothing -> loop state
          Just val -> loop (state{ replTerm = Just val, replContext = [] })
        else
        if takeExtension rest == ".cdl" then do
          fileCont <- lift $ Data.ByteString.readFile rest
          case decode fileCont :: Either String (DecompiledFile SourcePos Text Word64) of
            Left perr -> do
              outputStrLn perr
              loop state
            Right pval -> do
              let fvers = interpreterVersion (decompiledFileHeader pval)
              if fvers < version then do
                outputStrLn $ "cannot load file \"" ++ rest ++ "\n" ++
                  "compiler version of file:   " ++ showVersion fvers ++ "\n" ++
                  "compiler version of system: " ++ showVersion version
                loop state
                else do
                  let val = decompiledTerm pval
                  loop (state { replTerm = Just val, replContext = [] })
        else do
          outputStrLn $ "extension not recognized: " ++ rest
          loop state
    Just (':':'q':       _) -> return ()    
    Just (':':'r':' ':rest) ->
      case parseInput (pack rest) of
        Left perr -> do
          outputStrLn perr
          loop state
        Right pval -> do
          checked <- lift $ checkAndType pval (replOpts state) (replContext state)
          case checked of
            Nothing -> loop state
            Just _ -> do
              outputStrLn $ show . nfTerm $ pval
              loop state
    Just (':':'t':' ':rest) -> 
      case parseInput (pack rest) of
        Left perr -> do
          outputStrLn perr
          loop state
        Right pval -> do
          checked <- lift $ checkAndType pval (replOpts state) (replContext state)
          case checked of
            Nothing -> loop state
            Just _ ->
              case runReaderT (typeSynth pval) (replContext state) of
                Left err -> do
                  outputStrLn err
                  loop state
                Right val -> do
                  outputStrLn $ show val
                  loop state
    Just (':':'s':' ':rest) -> do
      let pOpts = Options.parseOptions (split rest " ")
      case parsedOptions pOpts of
        Nothing -> do
          case parsedError pOpts of
            Nothing -> do
              outputStrLn $ "an unknow error occured during proccessing of the options: "
                ++ "\n" ++ rest
              loop state
            Just err -> do
              outputStrLn err
              loop state
        Just opts -> loop (state {replOpts = opts})
    Just (':':'?':_) -> do
      outputStrLn "the turorial is under construction!"
      loop state
    Just input -> do
      outputStrLn $ "input : " ++ input ++ "\n not recognised"
      loop state

split :: String -> String -> [String]
split str pat = helper str pat [] [] where 
    helper :: String -> String -> String -> String -> [String]
    helper [] _  n _ = [n] ++ []
    helper xs [] n _ = [n] ++ (split xs pat)
    helper (x:xs) (y:ys) n m
        | x /= y = helper (xs) pat ((n++m)++[x]) m
        | otherwise = helper xs ys n (m++[y])
