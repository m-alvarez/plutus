{-# LANGUAGE OverloadedStrings #-}
module OptimizerSpec where

import           Common
import           TestLib

import           Language.PlutusIR.Optimizer.DeadCode
import           Language.PlutusIR.Parser
import           Language.PlutusIR.Transform.Rename   ()

optimizer :: TestNested
optimizer = testNested "optimizer" [
    deadCode
    ]

deadCode :: TestNested
deadCode = testNested "deadCode" [
    goldenPir removeDeadBindings term "typeLet"
    , goldenPir removeDeadBindings term "termLet"
    , goldenPir removeDeadBindings term "datatypeLiveType"
    , goldenPir removeDeadBindings term "datatypeLiveConstr"
    , goldenPir removeDeadBindings term "datatypeLiveDestr"
    , goldenPir removeDeadBindings term "datatypeDead"
    , goldenPir removeDeadBindings term "singleBinding"
    , goldenPir removeDeadBindings term "nestedBindings"
    , goldenPir removeDeadBindings term "nestedBindingsIndirect"
    , goldenPir removeDeadBindings term "recBindingSimple"
    , goldenPir removeDeadBindings term "recBindingComplex"
    ]
