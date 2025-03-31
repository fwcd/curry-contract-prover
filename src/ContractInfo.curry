module ContractInfo
  ( ContractInfo (..)
  , emptyContractInfo, showContractInfo, addPreCondToInfo, addPostCondToInfo
  ) where

data Cond = Cond
  { cName     :: String -- The pre/postcondition's name
  , cVerified :: Bool   -- Whether the condition could be verified
  }

-- TODO: Should we rename the type (and module, functions, ...) to ContractStats?

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

--- Shows the statistics in human-readable format.
showContractInfo :: ContractInfo -> String
showContractInfo ci =
  showStat "PRECONDITIONS : VERIFIED  " (verified (ciPreconds ci)) ++
  showStat "PRECONDITIONS : UNVERIFIED" (unverified (ciPreconds ci)) ++
  showStat "POSTCONDITIONS: VERIFIED  " (verified (ciPostconds ci)) ++
  showStat "POSTCONDITIONS: UNVERIFIED" (unverified (ciPreconds ci)) ++
  (if null (unverified (ciPreconds ci) ++ unverified (ciPostconds ci))
     then "\nALL CONTRACTS VERIFIED!"
     else "")
 where
  verified      = filter cVerified
  unverified    = filter (not . cVerified)
  showStat t fs = if null fs then "" else "\n" ++ t ++ ": " ++ unwords (cName <$> fs)

--- Adds an operation to the already processed preconditions.
addPreCondToInfo :: Cond -> ContractInfo -> ContractInfo
addPreCondToInfo c ci = ci { ciPreconds = c : ciPreconds ci }

--- Adds an operation to the already processed postconditions.
addPostCondToInfo :: Cond -> ContractInfo -> ContractInfo
addPostCondToInfo c ci = ci { ciPostconds = c : ciPostconds ci }
