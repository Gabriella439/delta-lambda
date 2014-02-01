{-# LANGUAGE NoMonomorphismRestriction, PackageImports, DeriveFoldable, 
             TupleSections #-}

module Delta_Lambda.Parser (parseTop, parseStringTerm, parseStringTop) where

import Data.Word (Word64)
import Delta_Lambda.Abstract
import Text.Parsec.Combinator (many1)
import qualified Text.Parsec.Token as P
import Text.Parsec.String (parseFromFile)
import Text.Parsec.Error (ParseError(..))
import Text.Parsec (getPosition, SourcePos)
import Text.Parsec.Prim (try, (<?>), parse, many)
import Text.Parsec.Language (LanguageDef, emptyDef)
import Text.Parsec.Char (letter, digit, oneOf, string)
import Control.Applicative ((<$>), (<*>), (*>), (<|>))

--below copied from Language.Scheme.Parser
lispDef :: LanguageDef ()
lispDef 
  = emptyDef { 
      P.reservedNames  = [],
      P.commentStart   = "(;",
      P.commentEnd     = ";)",
      P.commentLine    = ";",
      P.nestedComments = True,
      P.caseSensitive  = True,
      P.identStart     = letter <|> oneOf "!$%&|*+-\\/:<=>[]{}?@#^_~.",
      P.identLetter    = letter <|> digit <|> oneOf "!$%&|*+-\\/:<=>[]{}?@#^_~."
    }

lexeme = P.lexeme lexer
parens = P.parens lexer
brackets = P.brackets lexer
whiteSpace = P.whiteSpace lexer
identifier = P.identifier lexer
lexer = P.makeTokenParser lispDef

-- some quick helper functions
abstract p = flip $ foldr (\(i,t) -> Abstraction p i t . bind 1 i)
parameter = parens ((,) <$> identifier <*> expression)
parameters = parens (many1 parameter)

qualified = parens (string "qualified" *> (intersperse <$> many1 identifier))
            <?> "qualified identifier"
    where intersperse = foldr1 (\x y -> x ++ " " ++ y)

expression = typ <|> variable <|> try (parens expression) <|> try lambda
             <|> try apply <|> try letTop

typ = string "type" *> whiteSpace *> return Type <?> "type"

letTop =
    let lets = flip $ foldr Let
    in parens ((string "let" *> whiteSpace) *> 
               (lets <$> many1 top <*> expression))  <?> "let declaration"

top = try define <|> try declare <|> try section

section = parens ((string "namespace" *> whiteSpace) *>
                  parens (Namespace <$> getPosition <*>
                          parens (many1 identifier) <*>  many1 top))
          <?> "section"

declare = parens ((string "declare" *> whiteSpace) *>
         (assumption <$> getPosition <*> identifier <*> parameters'
                         <*> expression))
         <?> "declaration"
    where assumption p n a b = Declare p n $ abstract p a b
          parameters' = try parameters <|> return []

define = parens ((string "define" *> whiteSpace) *>
                 (definition <$> getPosition <*> identifier <*> parameters'
                                 <*> expression <*> expression))
         <?> "definition"
    where definition p n a t b = Define p n (abstract p a t) (abstract p a b)
          parameters'  = try parameters <|> return []

apply = application <$> getPosition <*> 
        parens ((:) <$> expression <*> many1 expression) <?> "application"
    where application p = foldl1 (Application p)

lambda = parens ((string "lambda" *> whiteSpace) *>
                 (abstract <$> getPosition <*> parameters <*> expression))
         <?> "lambda abstraction"

variable = Free <$> (try qualified <|> identifier) <*> getPosition
           <?> "variable"

parseStringTop = parse (whiteSpace *> many top) []
parseStringTerm = parse (whiteSpace *> expression) []
parseTop f = parseFromFile (whiteSpace *> many top) f
