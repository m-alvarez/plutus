{-# LANGUAGE DeriveAnyClass           #-}
{-# LANGUAGE DeriveGeneric            #-}
{-# LANGUAGE DerivingStrategies       #-}
{-# LANGUAGE DisambiguateRecordFields #-}
{-# LANGUAGE FlexibleContexts         #-}
{-# LANGUAGE FlexibleInstances        #-}
{-# LANGUAGE GADTs                    #-}
{-# LANGUAGE KindSignatures           #-}
{-# LANGUAGE NamedFieldPuns           #-}
{-# LANGUAGE PolyKinds                #-}
{-# LANGUAGE RankNTypes               #-}
{-# LANGUAGE StandaloneDeriving       #-}

{-# OPTIONS_GHC -fno-warn-orphans #-}

module LTL.Utils ( makeSM
                 , AbstractMachine
                 , Stack
                 , testSM
                 , funds
                 , currentSlot
                 , UserCommand (..)
                 , Cmd (..)
                 )
    where

import           GHC.Generics                  (Generic, Generic1)

import           Control.Lens                  (to, (^.))
import           Control.Monad
import           Control.Monad.Except          (ExceptT, runExceptT)
import           Control.Monad.State           (StateT, evalStateT, gets)
import           Control.Monad.Writer

import           Data.Foldable
import qualified Data.Map                      as Map
import           Data.TreeDiff

import qualified Ledger
import qualified Ledger.Ada                    as Ada
import qualified Ledger.Value                  as Value
import           Wallet.Emulator

import           Test.QuickCheck
import           Test.QuickCheck.Monadic
import           Test.StateMachine             hiding (cmdName)
import qualified Test.StateMachine.Types       as SM
import qualified Test.StateMachine.Types.Rank2 as SM

import qualified LTL

-- | A wrapper over a 'StateMachine' with default state, command and response types and an user-specified phase.
-- We refer to any 'StateMachine' that conforms to this type as an abstract machine.
type AbstractMachine phase m = StateMachine (State phase) (Command phase) m Response

-- | A constructor for abstract machines testing a certain LTL formula.
-- Note that, perhaps counterintuitively, the formula is itself part of the state machine, due to a quirk
-- of the implementation.
makeSM
    :: MonadEmulator m
    => [Wallet]
    -- ^ The list of wallets that the emulator should keep track of
    -- (i.e. what wallets to update on every newly minted block).
    -> (phase -> [Gen (UserCommand phase)])
    -- ^ A generator for user-specified commands that may depend on the current phase.
    -> phase
    -- ^ The initial value for the phase of this abstract machine.
    -> LTL.Formula (phase, EmulatorState)
    -- ^ The LTL formula to be verified.
    -> AbstractMachine phase m
makeSM wallets userGenerators initialPhase initialFormula =
    StateMachine
    { initModel = Initial initialPhase initialFormula
    , transition = \s (T c) r -> transition s c r
    , precondition = \s (T c) -> precondition s c
    , postcondition = \_ _ _ -> Top
    , invariant = Nothing
    , generator = fmap (fmap T) . generator userGenerators
    , distribution = Nothing
    , shrinker = shrinker
    , semantics = semantics wallets . getTrivial
    , mock = \_ _ -> return (Symbolic ())
    }

-- | Test an abstract function for a certain minimum number of steps, making sure that the machine's internal
-- property is verified throughout and at the end of the run.
testSM
    :: (Show phase, ToExpr phase)
    => AbstractMachine phase Stack
    -- ^ The state machine to be tested.
    -> Maybe Int
    -- ^ The minimum number of commands to generate.
    -- Note that due to a (known) bug in `quickcheck-state-machine`, this parameter currently does not work
    -- as intended (see [here](https://github.com/advancedtelematic/quickcheck-state-machine/issues/299)).
    -> EmulatorState
    -- ^ The initial state of the emulator from which to start the run.
    -> [Cmd phase]
    -- ^ A list of commands to be executed at the end of the machine-generated commands (for contracts that
    -- require a certain amount of steps to elapse in order to trigger, like the refund triggers in the
    -- crowdfunding example).
    -> Property
testSM sm minTrace es finally
    = forAllCommands sm minTrace $ \commands -> monadic (ioProperty . runStack) $ do
    let commands' = SM.Commands $ SM.unCommands commands
            ++ (SM.Command <$> (T <$> finally) <*> pure (Symbolic ()) <*> pure [])
    (hist, model, res) <- runCommands sm commands'
    case model of
        State (Concrete (_, f)) -> do
            monitor (counterexample (show commands'))
            prettyCommands sm hist $ res === SM.Ok .&&. LTL.finalize f === True
        Initial{}               -> pre False -- Discard traces of length zero
    where
        runStack :: Stack Property -> IO Property
        runStack input = do
            result <- evalStateT (runExceptT input) es
            case result of
                Left err -> return $ label ("Emulator error " ++ show err) False
                Right ok -> return ok

-- | Get the current funds of a wallet
funds :: Wallet -> EmulatorState -> Value.Value
funds wallet es = case Map.lookup wallet $ _walletStates es of
    -- TODO: fail gracefully in this case?
    Nothing -> error $ "Emulator error: no wallet " ++ show wallet ++ show (_walletStates es)
    Just ws -> foldl' Value.plus Value.zero $ fmap Ledger.txOutValue $ ws ^. ownFunds

-- | Get the current slot in the emulator.
currentSlot :: EmulatorState -> Ledger.Slot
currentSlot = (^. chainNewestFirst . to Ledger.lastSlot)

-- The shrinker for our state machine - as specified here, any command may be dropped during shrinking.
-- It is the responsibility of the user to write a precondition that ensures that commands remain valid after
-- shrinking.
shrinker :: State phase Symbolic -> cmd Symbolic -> [cmd Symbolic]
shrinker _ _ = []

-- | An user-specified command, possibly depending on some user-defined phase.
data UserCommand phase = UserCommand
    { cmdName         :: String
    -- ^ A printed representation of this command.
    , cmdPhase        :: phase -> phase
    -- ^ The effect of the command on the phase of the abstract machine.
    , cmdEffect       :: forall m . MonadEmulator m => m ()
    -- ^ The effect of the command on the emulator.
    , cmdPrecondition :: phase -> Logic
    -- ^ A precondition that a phase must satisfy before the command can be executed.
    }

-- State machine commands: either a block is minted or a user command is executed
data Cmd phase where
    Block :: Cmd phase
    User :: UserCommand phase -> Cmd phase
instance Show (Cmd phase) where
    show Block      = "Block"
    show (User cmd) = cmdName cmd

-- State transition for the abstract machine.
transition :: State phase r -> Cmd phase -> Response r -> State phase r
transition (Initial p _) Block (Symbolic ())                  = State $ Symbolic p
transition (Initial p f) Block (Concrete _)                   = State $ Concrete (p, f)
transition (State (Symbolic p)) Block (Symbolic ())           = State $ Symbolic p
transition (State (Concrete (p, f))) Block (Concrete es)      = State $ Concrete (p, LTL.step f (p, es))
transition (State (Symbolic p)) (User cmd) (Symbolic ())      = State $ Symbolic $ cmdPhase cmd p
transition (State (Concrete (p, f))) (User cmd) (Concrete es) = State $ Concrete (p', f')
    where p' = cmdPhase cmd p
          f' = LTL.step f (p, es)
transition Initial{} User{} _ = error "User transition in initial state"

-- Precondition for state machine commands.
-- Note that user commands can never be executed from the initial state.
precondition :: State phase Symbolic -> Cmd phase -> Logic
precondition _ Block                        = Top
precondition Initial{} User{}               = Bot
precondition (State (Symbolic p)) (User ua) = cmdPrecondition ua p

-- A generator for state machine commands.
-- Blocks can always be minted, the user provides a list of phase-specific generators for generating
-- extra commands.
generator :: (phase -> [Gen (UserCommand phase)]) -> State phase Symbolic -> Maybe (Gen (Cmd phase))
generator _ Initial{}                        = Just $ pure Block
generator userGenerator (State (Symbolic p)) = Just $ oneof $ pure Block : (fmap User <$> userGenerator p)

semantics :: MonadEmulator m => [Wallet] -> Cmd phase -> m (Response Concrete)
semantics wallets cmd = do
    case cmd of
        Block   -> processEmulated $ void $ processPending >>= walletsNotifyBlock wallets
        User ua -> cmdEffect ua
    gets Concrete

-- A type for commands that don't depend on whether they're executed against an abstract state (a phase)
-- or a concrete state (a phase plus a formula).
type Command phase = Trivial (Cmd phase)

-- The underlying state of our state machine.
-- It can be either an initial state that contains the initial phase and formula of the state machine,
-- an abstract state (used during generation) that contains the phase or a concrete state that keeps
-- track of the phase and the formula being tested.
data State phase (u :: * -> *) where
    Initial :: phase -> LTL.Formula (phase, EmulatorState) -> State phase u
    State   :: Choice phase (phase, LTL.Formula (phase, EmulatorState)) u -> State phase u
instance (Show phase) => Show (State phase u) where
    show Initial{}                           = "Initial"
    show (State (Symbolic phase))            = "Symbolic state " ++ show phase
    show (State (Concrete (phase, formula))) = "Concrete state (" ++ show phase ++ ", " ++ show formula ++ ")"
instance ToExpr phase => ToExpr (State phase Concrete) where
    toExpr Initial{}                 = App "Initial" []
    toExpr (State (Concrete (p, f))) = App "State" [toExpr p, toExpr f]

-- The underlying response of our state machine.
-- It can be either an abstract response (which is always just unit) or a concrete response that contains
-- the emulator state after executing the command.
type Response = Choice () EmulatorState
instance Show (Response SM.Symbolic) where
    show (Symbolic ()) = "OK"
-- Some pretty-printing for emulator states, as they're otherwise quite hard to make sense of.
instance Show (Response SM.Concrete) where
    show (Concrete es) = execWriter $ do
        tell "Blockchain\n"
        forM_ (es^.chainNewestFirst) $ \block -> do
            tell "\tBLOCK\n"
            forM_ block $ \tx ->
                tell $ "\t\t" ++ show tx ++ "\n"
        tell "UTXO\n"
        forM_ (Map.toList $ Ledger.getIndex $ es^.index) $ \(txOutRef, txOut) ->
                tell $ "\t" ++ show txOutRef ++ " => " ++ show txOut ++ "\n"
        tell "Wallet states\n"
        forM_ (Map.toList $ fundsDistribution es) $ \(w, v) ->
            tell $ "\t" ++ show (getWallet w) ++ " => " ++ show v ++ "\n"
        tell "Events\n"
        forM_ (_emulatorLog es) $ \e ->
            tell $ "\t" ++ show e ++ "\n"

-- quickcheck-state-machine forces some of our types to carry a parameter u which we often
-- don't need - the Trivial newtype extends a non-parametric type with a dummy type parameter
-- This is especially useful because we get all the instances for free
newtype Trivial (t :: *) (u :: * -> *) = T { getTrivial :: t }
    deriving (Generic, Generic1)
deriving anyclass instance CommandNames (Trivial t)
instance Show t => Show (Trivial t u) where
    show = show . getTrivial

instance SM.Functor (Trivial t) where
    fmap _ (T t) = T t
instance SM.Foldable (Trivial t) where
    foldMap _ _ = mempty
instance SM.Traversable (Trivial t) where
    traverse _ (T t) = pure (T t)

-- A sum-type that chooses its branch depending on a parameter that can be either Symbolic or Concrete.
data Choice (s :: *) (t :: *) (u :: * -> *) where
    Symbolic :: s -> Choice s t Symbolic
    Concrete :: t -> Choice s t Concrete
--deriving instance (Show s, Show t) => Show (Choice s t u)

instance SM.Foldable (Choice s t) where
    foldMap _ _ = mempty

-- A concrete monad for running Mockchain traces
type Stack = ExceptT AssertionError (StateT EmulatorState IO)

-- Some common useful ToExpr instances
instance ToExpr Wallet where
    toExpr (Wallet w) = App "Wallet" [ toExpr w ]
instance ToExpr Ledger.Ada where
    toExpr a = App "Ada" [ toExpr $ Ada.toInt a ]
