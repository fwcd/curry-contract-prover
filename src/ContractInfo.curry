module ContractInfo
  ( Cond (..), ContractInfo (..)
  , emptyContractInfo, showContractInfo, addPreCondToInfo, addPostCondToInfo
  ) where

import Text.Pretty (hcat, text, Doc)

data Cond = Cond
  { cName     :: String -- The pre/postcondition's name
  , cVerified :: Bool   -- Whether the condition could be verified
  }

-- TODO: Should we rename the type (and module, functions, ...) to ContractStats?

data ContractInfo = ContractInfo
  { ciPreConds  :: [Cond] -- The contract's preconditions
  , ciPostConds :: [Cond] -- The contract's postconditions
  }

emptyContractInfo :: ContractInfo
emptyContractInfo = ContractInfo
  { ciPreConds  = []
  , ciPostConds = []
  }

--- Shows the statistics in human-readable format.
showContractInfo :: ContractInfo -> Doc
showContractInfo ci = hcat
  [ showStat "PRECONDITIONS : VERIFIED  " (verified (ciPreConds ci))
  , showStat "PRECONDITIONS : UNVERIFIED" (unverified (ciPreConds ci))
  , showStat "POSTCONDITIONS: VERIFIED  " (verified (ciPostConds ci))
  , showStat "POSTCONDITIONS: UNVERIFIED" (unverified (ciPreConds ci))
  , text $ if null (unverified (ciPreConds ci) ++ unverified (ciPostConds ci))
     then "\nALL CONTRACTS VERIFIED!"
     else ""
  ]
 where
  verified      = filter cVerified
  unverified    = filter (not . cVerified)
  showStat t fs = text $ if null fs then "" else "\n" ++ t ++ ": " ++ unwords (cName <$> fs)

--- Adds an operation to the already processed preconditions.
addPreCondToInfo :: Cond -> ContractInfo -> ContractInfo
addPreCondToInfo c ci = ci { ciPreConds = c : ciPreConds ci }

--- Adds an operation to the already processed postconditions.
addPostCondToInfo :: Cond -> ContractInfo -> ContractInfo
addPostCondToInfo c ci = ci { ciPostConds = c : ciPostConds ci }
