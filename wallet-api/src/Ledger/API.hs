-- | The interface between application code and a blockchain implementation
module Ledger.API
    ( LedgerAPI (addTransaction, utxo, slot, reconcile)
    , WalletBackend (onSlot, cancel)
    , CallbackId (CallbackId)
    ) where

import           Data.Map (Map)
import           Ledger


newtype CallbackId = CallbackId Int

class LedgerAPI m where
    addTransaction :: Tx -> m ()

    -- We need to probe the current utxo - is this the right interface?
    utxo :: m (Map TxOutRef TxOut)
    slot :: m Slot

    -- I think this should be provided by concrete instances rather than the class
    -- Process all the pending transactions since the last slot and pick which get accepted
    reconcile :: m ()

class LedgerAPI m => WalletBackend m where
    -- We want some way of getting notifications from the ledger - is this the right interface?
    onSlot :: (CallbackId -> [Tx] -> [(Tx, ValidationError)] -> m ()) -> m CallbackId
    cancel :: CallbackId -> m ()
    -- Alternatively we could have every callback fire only once (in the immediately next slot) and
    -- if they need to keep running they can schedule themselves again

    -- Question: should this class be responsible for coin selection?
    -- Question: should this class be aware of who the user is?

-- We need something like this
fillTxn :: PubKey -> Tx -> Maybe Tx
fillTxn = undefined
-- It should pick inputs (owned by the user) in order to make the given transaction valid
-- The problem is, this may depend on e.g. pending transactions and the storage of these is up to
-- the implementation.

-- So we have two options

-- 1. use the current utxo set and implement fillTxn outside LedgerAPI - but the resulting transaction
-- may not be able to be validated if the user has submitted other transactions in the same slot.

-- 2. add this method to LedgerAPI and let each implementation do whatever's safe - this is annoying
-- because it duplicates work and may not be possible anyways (e.g. an implementation that gets this
-- stuff over the wire in real time)
