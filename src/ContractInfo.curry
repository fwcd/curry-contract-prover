module ContractInfo
  ( ContractInfo (..)
  , emptyContractInfo
  ) where

data ContractInfo = ContractInfo
  -- TODO: Is String the right type to represent pre-/postconditions here?
  { ciPreconds  :: [String] -- The contract's preconditions
  , ciPostconds :: [String] -- The contract's postconditions
  , ciHold      :: Bool     -- Whether the postconditions hold
  }

emptyContractInfo :: ContractInfo
emptyContractInfo = ContractInfo
  { ciPreconds  = []
  , ciPostconds = []
  , ciHold      = False
  }
