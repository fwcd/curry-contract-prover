module ContractInfo
  ( ContractInfo (..)
  , emptyContractInfo, addPreCondToInfo, addPostCondToInfo
  ) where

data Cond = Cond
  { cName     :: String -- The pre/postcondition's name
  , cVerified :: Bool   -- Whether the condition could be verified
  }

data ContractInfo = ContractInfo
  { ciPreconds  :: [Cond] -- The contract's preconditions
  , ciPostconds :: [Cond] -- The contract's postconditions
  , ciHold      :: Bool   -- Whether the postconditions hold
  }

emptyContractInfo :: ContractInfo
emptyContractInfo = ContractInfo
  { ciPreconds  = []
  , ciPostconds = []
  , ciHold      = False
  }

--- Adds an operation to the already processed preconditions.
addPreCondToInfo :: Cond -> ContractInfo -> ContractInfo
addPreCondToInfo c ci = ci { ciPreconds = c : ciPreconds ci }

--- Adds an operation to the already processed postconditions.
addPostCondToInfo :: Cond -> ContractInfo -> ContractInfo
addPostCondToInfo c ci = ci { ciPostconds = c : ciPostconds ci }
