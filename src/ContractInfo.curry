module ContractInfo
  ( Cond (..), ContractInfo (..)
  , emptyContractInfo, showContractInfo, allConds, addPreCondToInfo, addPostCondToInfo
  ) where

import Prelude hiding (empty)
import Text.Pretty (hcat, text, Doc, vcat, empty, (<>), (<+>), hsep, align)

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
showContractInfo ci = align $ vcat
  [ showStat "  VERIFIED"   (verified (allConds ci))
  , showStat "UNVERIFIED" (unverified (allConds ci))
  ]
 where
  verified      = filter cVerified
  unverified    = filter (not . cVerified)
  showStat t fs = if null fs then empty else text t <> text ":" <+> hsep (text . cName <$> fs)

allConds :: ContractInfo -> [Cond]
allConds ci = ciPreConds ci ++ ciPostConds ci

--- Adds an operation to the already processed preconditions.
addPreCondToInfo :: Cond -> ContractInfo -> ContractInfo
addPreCondToInfo c ci = ci { ciPreConds = c : ciPreConds ci }

--- Adds an operation to the already processed postconditions.
addPostCondToInfo :: Cond -> ContractInfo -> ContractInfo
addPostCondToInfo c ci = ci { ciPostConds = c : ciPostConds ci }
