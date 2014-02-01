{-# LANGUAGE PackageImports #-}
module Delta_Lambda.Main where

import System.IO
import System.Environment
import Delta_Lambda.Parser
import System.Console.Haskeline
import "mtl" Control.Monad.Error
import Delta_Lambda.Abstract hiding (bind)
import "mtl" Control.Monad.Reader (ReaderT(..))

-- a lot of this is taken from "write yourself a scheme in 48 hours"

data ReplState a = ReplState {
  withContext :: [Term a]
}

defaultRepl :: (Show a) => ReplState a
defaultRepl = ReplState {
  withContext = []
}

flushStr :: String -> IO ()
flushStr s = putStr s >> hFlush stdout

readPrompt :: String -> IO String
readPrompt prompt = flushStr prompt >> getLine

checkCorrect :: (Monad m, Show a) => [Term a] -> [Term a] -> m [Char]
checkCorrect (x:xs) e = 
    case runReaderT (correct x) e of
      Left err -> return $ "|- invalid\n" ++ err
      Right _ -> checkCorrect xs (e ++ [x])
checkCorrect [] e = return $ "|- correct\n"

evalString :: String -> ReplState String -> IO String
evalString s replState =
    case parseString s of
      Left err -> return $ show err
      Right val -> checkCorrect val (withContext replState)

evalFile :: ReplState String -> String -> IO ()
evalFile replState s =
    do parsed <- parseFile s
       case parsed of
         Left e -> putStrLn . show $ e
         Right val -> checkCorrect val (withContext replState) >>= putStrLn

evalAndPrint :: ReplState String -> String  -> IO ()
evalAndPrint replState e = evalString e replState >>= putStrLn

until_ :: Monad m => (a -> Bool) -> m a -> (a -> m ()) -> m ()
until_ pred prompt action =
    do result <- prompt
       if pred result then return ()
       else action result >> until_ pred prompt action

runRepl :: IO ()
runRepl = until_ (== "quit") (readPrompt "|- ") (evalAndPrint defaultRepl)



main :: IO ()
main =
    do args <- getArgs
       case length args of
         0 -> runRepl
         1 -> evalFile defaultRepl $ args !! 0
         n -> putStrLn "multiple file inputs not yet supported"

