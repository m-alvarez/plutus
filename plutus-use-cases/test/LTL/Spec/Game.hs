{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase       #-}
{-# LANGUAGE TemplateHaskell  #-}

module LTL.Spec.Game where

import           Control.Lens                                  hiding (elements)
import           Control.Monad

import           Data.List
import           Data.Map                                      (Map)
import qualified Data.Map                                      as Map
import           Data.Maybe
import           Data.TreeDiff

import           Test.QuickCheck
import           Test.StateMachine.Logic                       (Logic (..))

import           Ledger
import qualified Ledger.Ada                                    as Ada
import           Wallet.API                                    (PubKey (..))
import           Wallet.Emulator

import qualified LTL
import           LTL.Utils

import           Language.PlutusTx.Coordination.Contracts.Game (guess, lock, startGame)

data Phase = Phase
    { _players :: [Wallet]
    , _game    :: Maybe (Wallet, Ada, String)
    , _winners :: [Wallet] -- More than one player may make the same correct guess within a block!
    } deriving (Show)
makeLenses ''Phase
instance ToExpr Phase where
    toExpr (Phase p g w) = App "Phase" [ toExpr p, toExpr g, toExpr w ]

initialPhase :: Phase
initialPhase = Phase [] Nothing []

wallets :: [Wallet]
wallets = Wallet <$> [1 .. 3]

startingBalances :: Map PubKey Value
startingBalances = Map.fromList $ zip (walletPubKey <$> wallets) (repeat startingBalance)

startingBalance :: Value
startingBalance = Ada.adaValueOf 10000

gameSM :: MonadEmulator m => AbstractMachine Phase m
gameSM = makeSM wallets generator initialPhase formula

test :: Property
test = testSM gameSM (Just 30) es waitBlocks
    where waitBlocks = replicate 1 Block
          es = emulatorStateInitialDist startingBalances

formula :: LTL.Formula (Phase, EmulatorState)
formula =
    -- Check that if the correct guess is never hit, everyone's money is the starting amount
    LTL.InSequence [guessCorrect, payout] `LTL.or` LTL.Always (incorrectGuess `LTL.and` nobodyGetsMoney)
    where guessCorrect = LTL.label "correct guess" $
              LTL.atom (\(phase, _) -> not $ null $ phase^.winners)
          -- The payout is only positive if the wallet wasn't the host
          payout = LTL.Label "payout" $
                   LTL.atom (\case (Phase _ (Just (host, prize, _)) win, es) ->
                                       flip any win $
                                       \w -> funds w es ==
                                             if host == w
                                             then startingBalance
                                             else startingBalance <> Ada.toValue prize
                                   _ -> False)
          incorrectGuess = LTL.label "no correct guesses so far" $
              LTL.atom (\(phase, _) -> null $ phase^.winners)
          nobodyGetsMoney = LTL.label "nobody receives the payout" $
              LTL.atom (\(_, es) -> any (\w -> funds w es <= startingBalance) wallets)

lockFundsCmd :: Wallet -> Ada -> String -> UserCommand Phase
lockFundsCmd w ada str = UserCommand
    { cmdName = "Lock funds " ++ show (w, ada, str)
    -- Whoever hosts the game is automatically an active player
    , cmdPhase = (game ?~ (w, ada, str)) . over players ([w] `union`)
    , cmdEffect = processEmulated $ void $ walletAction w (lock str ada) >> updateAll
    , cmdPrecondition = \p ->
            Boolean $ isNothing $ p^.game
    }
    where updateAll = processPending >>= void . walletsNotifyBlock wallets

-- whoever plays can't be the host
startGameCmd :: Wallet -> UserCommand Phase
startGameCmd w = UserCommand
    { cmdName = "Start game " ++ show w
    , cmdPhase = \phase ->
            -- Users can only join a game before it starts
            case phase^.game of
                Nothing -> phase & over players ([w] `union`)
                Just _  -> phase
    , cmdEffect = processEmulated $ void $ walletAction w startGame
    , cmdPrecondition = const Top
    }

-- Future correct guesses shouldn't override the first correct guess - except within the same block?!
guessCmd :: Wallet -> String -> UserCommand Phase
guessCmd w str = UserCommand
    { cmdName = "Guess " ++ show w ++ " " ++ show str
    , cmdPhase = \phase ->
            case phase^.game of
                Nothing -> phase
                Just (_, _, str')
                    | str == str' && w `elem` phase^.players -> over winners ([w] `union`) phase
                    | otherwise -> phase
    , cmdEffect = processEmulated $ void $ walletAction w (guess str)
    , cmdPrecondition = const Top
    }

generator :: Phase -> [Gen (UserCommand Phase)]
generator (Phase _ g _) = genLock ++ genStart ++ genGuess
    where genLock = pure $ lockFundsCmd <$> elements wallets <*> (Ada.fromInt <$> choose (1, 200)) <*> arbitrary
          genStart = pure $ startGameCmd <$> elements wallets
          genGuess = case g of
              -- Make sure not to guess the right answer twice!
              Just (_, _, str') -> [guessRight str', guessWrong str']
              _                 -> [randomGuess]
          randomGuess = guessCmd <$> elements wallets <*> arbitrary
          guessRight str = guessCmd <$> elements wallets <*> pure str
          guessWrong str = guessCmd <$> elements wallets <*> arbitrary `suchThat` (/= str)
