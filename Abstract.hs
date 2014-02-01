{-# LANGUAGE PackageImports, OverloadedStrings, BangPatterns,
             StandaloneDeriving  #-}
module Delta_Lambda.Abstract (
  TC, Top(..), Term (..), subst, nf, whnf, correct, typing,
  typeOf, betaEq, bind, prettyTop, prettyTerm)
where --for now we dont export things that are marked TODO.
      --  (so I dont get ahead of myself)

import Data.Complex
import Data.Word (Word64)
import Prelude hiding (tail)
import Control.Parallel (par)
import qualified Prelude as P
import "mtl" Control.Monad.Trans
import Data.String (IsString(..))
import Text.Parsec.Pos (SourcePos)
import Text.PrettyPrint.Leijen hiding (pretty)
import "mtl" Control.Monad.Reader (ReaderT, ask, local)
import "mtl" Control.Monad.Error (throwError, Error(..), MonadError(..))

--TODO: implement a propper prelude so that I can typecheck constants and
--      primatives
data Constant a = List [Term a]
                | String String
                | Natural Word64
                | Character Char
                | Integer Integer
                | Floating Double
                | Rational Rational
                | Complex (Complex Double)
                  deriving(Show, Eq)

data Primative a = PrimOp String
                 | Constant (Constant a)
                   deriving (Show, Eq)

data Top a = Declare SourcePos a (Term a)
           | Namespace SourcePos [a] [Top a] -- not folded into Terms yet
           | Define SourcePos a (Term a) (Term a)
             deriving (Show, Eq)

data Term a = Type
            | Free a SourcePos --free variables
            | Let (Top a) (Term a)
            | Primative (Primative a) -- to be implemented when a prelude is
            | Bound (Word64, a) SourcePos --bound variables
            | Application SourcePos (Term a) (Term a)
            | Abstraction SourcePos a (Term a) (Term a)
              deriving (Show)

type TC = Either String

--------------------------------------------------------------------------------
--------------------------------------------------------------------------------
-- this section contains the untyped portion of the calculus

{- this function updates a terms bound variables, k tests for free variables
   (essentailly ones not bound in the current scope, not actual 'Free'),
   and i - 1 is the value by which a variable, if free must be incremented. -}
update :: Word64 -> Word64 -> Term a -> Term a
update k i (Bound (v, a) p)
    | v >  k = Bound (v + i - 1, a) p
    | v <= k = Bound (v, a) p
update k i (Application p a b) =
    let a' = update k i a
        b' = a' `par` update k i b
    in Application p a' b'
update k i (Abstraction p n a b) =
    let a' = update k i a
        b' = a' `par` update (1 + k) i b
        {- when we pass under a binder, we have
        to increment because, the variable
        we are looking for is in a higher
        scope. -}
    in Abstraction p n a' b'
update _ _ e = e

subst :: Word64 -> Term a -> Term a -> Term a
subst subject replacement = subst'
    where subst' e@(Bound (v, a) p) =
              case compare v subject of
                   -- variable isn't bound, but we are replacing a variable
                   -- (effectively removing a binding scope) so decrease
                   GT -> Bound (v - 1, a) p
                   -- this is the variable we are wanting to substitute
                   -- update the free variable in the replacement so they
                   -- dont accidentally get bound by (newly) surrounding lambdas
                   EQ -> update 0 subject replacement
                   -- this variable is local to another binder, ignore it
                   LT -> e
          subst' (Application p a b) =
              let a' = subst' a
                  b' = a' `par` subst' b
              in Application p a' b'
          subst' (Abstraction p n a b) =
              let a' = subst' a
                  -- going under a binder, subject is free here so increment
                  b' = a' `par` subst (1 + subject) replacement b
              in Abstraction p n a' b'
          subst' e = e

-- this instance essentally is alpha equivalence, and this is obvious for
-- de Bruijn binders, as alpha equivalent terms have the same de Bruijn indices
-- in their structure. free variables are not considered as they could be
-- evenutally bound by differing binders, distorting the original equivalence.
instance Eq a => Eq (Term a) where
  Type == Type = True
  Primative e == Primative e' = e == e'
  Free _ _ == Free _ _ = False
  Bound (v, _) _ == Bound (v', _) _ = v == v'
  Application _ a b == Application _ a' b' = 
      let at = a' == a
          bt = at `par` (b' == b)
      in at && bt
  Abstraction _ _ a b == Abstraction _ _ a' b' =
      let at = a' == a
          bt = at `par` (b' == b)
      in at && bt
  _ == _ = False

-- this essentailly makes free variables bound to a particular binder.
-- only really used by the parser.
bind :: (Eq a) => Word64 -> a -> Term a -> Term a
bind i a (Free a' p)
    | a == a' = Bound (i, a) p
    | otherwise = Free a' p
bind i a (Application p x y) =
  let x' = bind i a x
      y' = x' `par` bind i a y
  in Application p x' y'
bind i a (Abstraction p n x y) =
  let x' = bind i a x
      y' = x' `par` bind (i + 1) a y
  in Abstraction p n x' y'
bind i a e@_ = e

-- weak head normal form of a term, essentually, there are no immidiate redecies
-- in the spine of the term, only un-applicable abstractors, or applicators
whnf :: Term a -> Term a 
whnf (Application p a b) =
    case whnf a of
      Abstraction _ _ _ a' -> whnf $ subst 1 a a'
      f -> Application p a f
whnf e@_ = e

-- normal form of a term, this is the computational equivalent to the symmetric
-- transitive closure of beta reduction (and it's coresponding reduction context
-- rules).
nf :: Term a -> Term a 
nf (Abstraction p n a b) = Abstraction p n (nf a) $ nf b
nf (Application p a b) =
    case whnf a of
      Abstraction _ _ _ f -> nf $ subst 1 a f
      f -> let a' = nf a
               f' = a' `par` nf f
           in Application p a' f'
nf e@_ = e

-- this should be obvious
betaEq :: Eq a => Term a -> Term a -> Bool
betaEq a b = nf a == nf b

--------------------------------------------------------------------------------
--------------------------------------------------------------------------------
-- this section contains the typing relations

-- for more information regaurding the reasoning behind the definitions of the
-- following structural relation on terms see:
--
-- Defining lambda-Typed lambda-Calculi by Axiomatizing the Typing Relation
-- Philippe de Groote

-- provides the final type of a term, this iterated form of the typeOf function
-- is related to eta-expansion of a term.
typing :: (Show a, Eq a) => Term a -> ReaderT [Term a] TC (Term a)
typing x = degree x >>= \deg -> typeN x deg

-- this function computes the 'level' of dependency a term has on it's
-- parents. I.E. if given a term '[x:type]type' it produces a value of 0
-- as the body of the function has no dependency on the parameter however,
-- if we are given '[x:type]x' the function produces a value of 1, as the
-- function body has a 1 level dependency on it's parameter.
-- likewise '[x:type][y:x]y' produces a value of 2 and '[x:type][y:x]x' a
-- value of 1, etc...
-- this function, essentailly computes the number of times the typeOf function
-- must be applied to a term in order to propperly eta-expand it.
degree :: (Show a, Eq a) => Term a -> ReaderT [Term a] TC Word64
degree x =
    let tail :: Term a -> Term a
        tail (Abstraction _ _ _ b) = tail b
        tail (Application _ b _) = tail b
        tail e@_ = e
    in if tail x == Type then return 0
       else do x' <- typeOf x >>= \t -> degree t
               return $ 1 + x'

-- the function that does all the hard work of the typing function.
-- (actually contains the logic for iteration)
typeN :: (Show a, Eq a) => Term a -> Word64 -> ReaderT [Term a] TC (Term a)
typeN x 0 = return x
typeN x n = typeOf x >>= \xt -> typeN xt (n - 1)

-- calculates the type of a term, note the term produced by this function is
-- beta equivalent to the term produced by the inferental definition of
-- the calculus's typing judgements.
typeOf :: (Show a) => Term a -> ReaderT [Term a] TC (Term a)
typeOf Type = throwError "type has no (super) type"
typeOf (Free v p) =
    throwError $ "free variable : " ++ printT v ++ " " ++ printT p
typeOf (Bound (i, n) p) =
    do context <- ask
       if length context >= fromIntegral i then
           return $ update 0 i $ context !! (fromIntegral i - 1)
       else throwError $ "bound variable points beyond context: " 
                ++ printT n ++ " " ++ printT p
typeOf (Abstraction p n t b) =
    do b' <- local (t:) (typeOf b)
       return $ Abstraction p n t b'
typeOf (Application p f a) =
    do f' <- typeOf f
       return $ Application p f' a

-- this function is equivalent (when packaged with the above functions) to the
-- inferental typing judgements. I must elide proof of this for now, as it is
-- REALLY hard to do.
correct :: (Show a, Eq a) => Term a -> ReaderT [Term a] TC ()
correct Type = return ()
correct (Free v p) =
    throwError $ "free variable : " ++ printT v ++ " " ++ printT p
correct (Bound (i, n) p) =
    do context <- ask
       if length context >= fromIntegral i then
           -- this is just in case I've gotten the context position math wrong
           -- once I know it's correct I'll remove it
           correct $ update 0 i $ context !! fromIntegral i
           -- return ()
       else throwError $ 
                "bound variable points beyond context: " ++ printT n ++ " "
                ++ printT p
correct (Abstraction p n t b) =
    do correct t
       b' <- local (t:) (correct b)
       return b'
correct (Application p f a) =
    do deg <- correct a >> degree a -- the degree of the argument must be > 1
       if deg < 1 then throwError $ "attempting to apply a type to a function"
       else -- the typing function wont work if degree a < 1
           do a' <- typeOf a -- proof that the typeOf and typing relations
              f' <- typing f -- preserve correctness must be elided for now
              case nf f' of
                Abstraction p' n t b ->
                    do _ <- correct t
                       if betaEq t a'
                       -- this implements subject expansion, as a function is
                       -- is considered correct before and after substitution
                       -- (and typing) this is because the typing relation 
                       -- preserves correctness iff the term is orginally
                       -- correct.
                       then correct $ subst 1 a b
                       else throwError $
                         "function parameter and argument type" 
                         ++ " don't agree:\n" ++ "argument: " ++
                         show p ++ " function: " ++ show p'
                _ -> throwError $ "attempted to apply to a non-function: " ++
                     show p

raise :: Term a -> Term [a]
raise Type = Type
raise (Bound (i, n) p) = Bound (i, [n]) p
raise (Free n p) = Free [n] p
raise (Application p a b) = Application p (raise a) (raise b)
raise (Abstraction p n t b) = Abstraction p [n] (raise t) (raise b)

--TODO: implement namespaces as a transform on the ast bound names
--TODO: implement Top level expressions as simplified Terms
transformTop :: (Eq a) => [a] -> [Top a] -> Term [a]
transformTop ns ((Declare p n t):ts) =
    Abstraction p (ns ++ [n]) (raise t) $ bind 1 (ns ++ [n]) $
    transformTop ns ts
transformTop ns ((Define p n t b):ts) =
    Application p (raise b) $ Abstraction p (ns ++[n]) (raise t) $
    bind 1 (ns ++ [n]) $ transformTop ns ts
transformTop ns ((Namespace p n b):ts) =
    let b' = transformTop (ns ++ n) b
        strip f bv (Abstraction p n t b) =  -- \/ ----- could be: (bv ++ [n]) ?
            strip (f . (Abstraction p n t)) (n:bv) b
        strip f bv (Application p g a) =
            strip (f . (Application p g)) bv a
        strip f bv e = (f, bv, e)
        (f, bv, _) = strip id [] b'
    --TODO test that this is the proper ordering on bindings (should be foldl?)
    in f $ foldr (bind 1) (transformTop ns ts) bv
transformTop _ [] = Type

--------------------------------------------------------------------------------
--------------------------------------------------------------------------------
-- the below is a series of pretty printing functions that are of no real value
-- to the implementation of the calculus's correctness, so for now no
-- documentation shall be provided.

printNS :: (Show a) => [a] -> String
printNS x = concat (map (++" ") (init $ map printT x) ++ [printT $ last x])

--needed because if we use a string type as our free variable quotes show up...
removeQuotes :: String -> String
removeQuotes x
    | not (null x) && head x == '"' && last x == '"' =
        init . P.tail $ x
    | otherwise = x

printT :: Show a => a -> String
printT = removeQuotes . show

prettyTerm x = displayS (renderPretty 0.5 80 $ ppTerm x) ""
prettyTop x = displayS (renderPretty 0.5 80 $ ppTop x) ""

cleanName :: (Show a) => a -> Doc
cleanName = text . printT

ppTerm :: (Show a) => Term a -> Doc
ppTerm Type = text "type"
ppTerm (Free v _) =
    if ' ' `elem` displayS (renderPretty 0.5 80 $ cleanName v) "" then
        parens (text "qualified" <+> cleanName v)
    else cleanName v
ppTerm (Bound (_, a) _)= text . removeQuotes . show $ a
ppTerm (Application _ a b) = parens (hsep $ agrigateArgs [ppTerm a] b)
ppTerm (Abstraction _ n a b) =
    let (args, body) = agrigateParams [ppPair n a] b
        ppParen f a = if length a == 1 then f a else parens $ f a
    in parens (text "lambda" <+> ppParen (align . vcat) args <+> body)
ppTerm (Let d b) =
    let (defs, body) = agrigate [ppTop d] b
        ppParen f a = if length a == 1 then f a else parens $ f a
        agrigate as (Let d' b') = agrigate (as ++ [ppTop d']) b'
        agrigate as b' = (as, ppTerm b')
    in parens (text "let" <+> ppParen (align . vcat) defs <+> body)

ppPair n t = parens (cleanName n <+> ppTerm t)

agrigateParams as (Abstraction _ n t b) =
    agrigateParams (as ++ [ppPair n t]) b
agrigateParams as e = (as, ppTerm e)

agrigateArgs as (Application _ a b) = agrigateArgs (as ++ [ppTerm a]) b
agrigateArgs as e = as ++ [ppTerm e]

ppTop (Declare _ n t) =
    let (args, body) = agrigateParams [] t
    in parens (text "assume" <+> cleanName n <+> hcat args <+> body)
ppTop (Define _ n t v) =
    let (args, typed) = agrigateParams [] t
        (_, body) = agrigateParams [] v
    in parens (text "define" <+> cleanName n <+> parens (align . hcat $ args)
               <+> typed <+> body)
ppTop (Namespace _ name body) =
    parens (text "namespace" <+> parens (hcat $ map cleanName name)
                     <+> parens (align . vcat $ map ppTop body))
