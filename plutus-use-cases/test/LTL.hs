{-# LANGUAGE GADTs           #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ViewPatterns    #-}
module LTL ( Formula(..)
           , bool, atom, change, stepsThen
           , and, or, not, label, eventually, inSequence
           , step, finalize)
where

import           Data.TreeDiff
import           Prelude       hiding (and, not, or)
import qualified Prelude

data Formula a = Grab (a -> Formula a)
               | And (Formula a) (Formula a)
               | Or (Formula a) (Formula a)
               | Not (Formula a)
               | Next (Formula a)
               | Always (Formula a)
               | InSequence [Formula a]
               | T
               | F
               | Label String (Formula a)

pattern Strip :: Formula a -> Formula a
pattern Strip a <- (strip -> a)

bool :: Bool -> Formula a
bool True  = T
bool False = F

atom :: (a -> Bool) -> Formula a
atom = Grab . (bool .)

instance Show (Formula a) where
    show _ = "<formula>"

instance ToExpr (Formula a) where
    toExpr (Grab _)          = App "Atom" []
    toExpr (And f1 f2)       = App "And" [toExpr f1, toExpr f2]
    toExpr (Or f1 f2)        = App "Or" [toExpr f1, toExpr f2]
    toExpr (Not f1)          = App "Not" [toExpr f1]
    toExpr (Next f1)         = App "Next" [toExpr f1]
    toExpr (Always f1)       = App "Always" [toExpr f1]
    toExpr (InSequence [f1]) = App "Eventually" [toExpr f1]
    toExpr (InSequence fs)   = App "InSequence" $ map toExpr fs
    toExpr T                 = App "T" []
    toExpr F                 = App "F" []
    toExpr (Label s f)       = App s [toExpr f]

-- Demonstrating how to encode a step-wise change using LTL formulae and Grab
change :: (Eq a) => (a -> a) -> Formula a
change f = Grab $ \old -> Next $ atom (== f old)

stepsThen :: Int -> Formula a -> Formula a
n `stepsThen` f
    | n < 0     = F
    | n == 0    = f
    | otherwise = Next $ (n-1) `stepsThen` f

strip :: Formula a -> Formula a
strip (Label _ f) = strip f
strip f           = f

and :: Formula a -> Formula a -> Formula a
and (Strip F) _  = F
and (Strip T) f2 = f2
and _ (Strip F)  = F
and f1 (Strip T) = f1
and f1 f2        = And f1 f2

or :: Formula a -> Formula a -> Formula a
or (Strip T) _  = T
or (Strip F) f2 = f2
or _ (Strip T)  = T
or f1 (Strip F) = f1
or f1 f2        = Or f1 f2

not :: Formula a -> Formula a
not (Strip T) = F
not (Strip F) = T
not f         = Not f

label :: String -> Formula a -> Formula a
label = Label

eventually :: Formula a -> Formula a
eventually = InSequence . pure

inSequence :: [Formula a] -> Formula a
inSequence []           = T
inSequence (Strip T:fs) = inSequence fs
inSequence fs           = InSequence fs

stepSequence :: [Formula a] -> a -> Formula a
stepSequence [] _ = T
stepSequence f@(f1:fs) a =
    case step f1 a of
        Strip T -> stepSequence fs a
        Strip F -> InSequence f
        f1'     -> (f1' `and` inSequence fs) `or` InSequence f

step :: Formula a -> a -> Formula a
step (Grab h) a        = h a
step (And f1 f2) a     = step f1 a `and` step f2 a
step (Or f1 f2) a      = step f1 a `or` step f2 a
step (Not f1) a        = not $ step f1 a
step (Next f1) _       = f1
step (Always f1) a     = step f1 a `and` Always f1
step (InSequence fs) a = stepSequence fs a
step (Label s f1) a    = Label s (step f1 a)
step T _               = T
step F _               = F

finalize :: Formula a -> Bool
finalize (Grab _)        = False -- TODO: is this the right semantics?
finalize (And f1 f2)     = finalize f1 && finalize f2
finalize (Or f1 f2)      = finalize f1 || finalize f2
finalize (Not f)         = Prelude.not $ finalize f
finalize (InSequence fs) = all finalize fs
finalize (Next _)        = False
finalize (Always _)      = True
finalize T               = True
finalize F               = False
finalize (Label _ f1)    = finalize f1
