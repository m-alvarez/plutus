{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
module Tester where

import           Control.Monad
import           Control.Monad.Except

class (Monad m) => Machine m e | m -> e where
    interpret :: m a -> ExceptT e IO a

class (Machine m e) => Abstract state m e | state -> m where
    reify :: m state

runProgram :: Abstract s m e => [m ()] -> m [s]
runProgram = mapM (>> reify)

data Value state a = Now (state -> a)
                   | Next (Value state a)

data Predicate state = Prop (Value state Bool)
                     | Step (Predicate state)
                     | And [Predicate state]
                     | Or [Predicate state]
                     | Eventually (Predicate state)
                     | Always (Predicate state)
                     | When (Predicate state) (Predicate state)

value :: Value state a -> [state] -> a
value (Now f) (s:_)   = f s
value (Next v) (_:s') = value v s'
value _ []            = undefined

holds :: Predicate state -> [state] -> Bool
holds (Prop p) s            = value p s
holds (Step p) s            = holds p $ tail s

holds (And _) []            = False -- TODO is this correct?
holds (And ps) s            = all (`holds` s) ps

holds (Or _) []             = False -- TODO is this correct?
holds (Or ps) s             = any (`holds` s) ps

holds (Eventually p) (s:s') = holds p (s:s') || holds (Eventually p) s'
holds (Eventually _) []     = False

holds (Always p) (s:s')     = holds p (s:s') && holds (Always p) s'
holds (Always _) []         = True

holds (When p q) s          =  not (holds p s) || holds q s
