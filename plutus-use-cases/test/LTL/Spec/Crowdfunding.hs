{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs            #-}
{-# LANGUAGE NamedFieldPuns   #-}
{-# LANGUAGE RecordWildCards  #-}
{-# LANGUAGE TemplateHaskell  #-}
{-# OPTIONS_GHC -fno-warn-incomplete-uni-patterns #-}
{-# OPTIONS_GHC -fno-warn-unused-do-bind #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# OPTIONS_GHC -fno-warn-unused-local-binds #-}
module LTL.Spec.Crowdfunding where

import           Prelude                                               hiding (and, not, or)

import           Control.Lens                                          hiding (elements)
import           Control.Monad                                         (void)

import           Data.Map                                              (Map)
import qualified Data.Map                                              as Map
import           Data.TreeDiff

import           LTL                                                   hiding (Formula (..))
import qualified LTL
import           LTL.Utils

import           Test.QuickCheck                                       hiding (collect, generate)
import qualified Test.StateMachine.Logic                               as Logic

import           Wallet.Emulator

import qualified Language.PlutusTx.Coordination.Contracts.CrowdFunding as CF
import           Ledger
import           Ledger.Ada                                            (Ada)
import qualified Ledger.Ada                                            as Ada
import           Ledger.Value                                          (Value)

data Phase = Phase
    { _fundsCollected    :: Ada
    , _collectionStarted :: Bool
    }
    deriving (Show)
makeLenses ''Phase
instance ToExpr Phase where
    toExpr (Phase n started) = App "Phase" [toExpr n, toExpr started]

contrib :: Wallet -> Ada -> CF.Campaign -> UserCommand Phase
contrib w ada cmp = UserCommand
    { cmdName = "Wallet " ++ show (getWallet w) ++ " contributes " ++ show (Ada.toInt ada)
    , cmdPhase = over fundsCollected (ada +)
    , cmdEffect = processEmulated $ void $ walletAction w (CF.contribute cmp ada)
    , cmdPrecondition = Logic.Boolean . (^. collectionStarted)
    }

collect :: Wallet -> CF.Campaign -> UserCommand Phase
collect w cmp = UserCommand
    { cmdName = "Wallet " ++ show (getWallet w) ++ " collects funds"
    , cmdPhase = collectionStarted .~ True
    , cmdEffect = processEmulated $ void $ walletAction w (CF.collect cmp)
    , cmdPrecondition = const Logic.Top
    }

generate :: Phase -> [Gen (UserCommand Phase)]
generate phase = donation : doCollect
    where donation = contrib <$> elements (tail wallets) -- avoid donations from the campaign organizer
                             <*> (Ada.fromInt <$> choose (50, 500))
                             <*> pure campaign
          doCollect = if phase^.collectionStarted
                      then []
                      else [pure $ collect owner campaign]

test :: Property
test = testSM sm (Just 30) es waitBlocks
    where waitBlocks = replicate 15 Block
          es = emulatorStateInitialDist balances
          sm = makeSM wallets generate initialPhase formula

formula :: LTL.Formula (Phase, EmulatorState)
formula =
    LTL.InSequence [deadlineExpires, reset] `or` LTL.eventually getsMoney
    where getsMoney = LTL.label "gets money" $
              LTL.Grab (\(phase, es) -> LTL.Next $ atom $ \(_, es') ->
                               Ada.fromValue (funds owner es')
                               == Ada.fromValue (funds owner es) + phase^.fundsCollected)
          deadlineExpires = LTL.label "deadline expires" $
              LTL.Grab $ \(phase, es) ->
                             LTL.bool $ phase^.fundsCollected < CF.campaignTarget campaign
                                        && currentSlot es >= CF.campaignDeadline campaign
          reset = LTL.Label "reset" $
              LTL.Grab $ \(_, es) ->
              LTL.bool $ all (Ada.fromValue startingBalance ==) [Ada.fromValue (funds w es) | w <- wallets]

initialPhase :: Phase
initialPhase = Phase 0 False

wallets :: [Wallet]
wallets = Wallet <$> [1 .. 3]

balances :: Map PubKey Value
balances = Map.fromList $ zip (walletPubKey <$> wallets) (repeat startingBalance)

startingBalance :: Value
startingBalance = Ada.adaValueOf 10000

campaign :: CF.Campaign
campaign = CF.Campaign
    { campaignDeadline = 10
    , campaignTarget = 1000
    , campaignCollectionDeadline = 15
    , campaignOwner = walletPubKey owner
    }

owner :: Wallet
owner = Wallet 1

instance Show CF.Campaign where
    show _ = ""
