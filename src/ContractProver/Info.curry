module ContractProver.Info
  ( Cond (..), ContractInfo (..)
  , emptyContractInfo, ppContractInfo, allConds, addPreCondToInfo, addPostCondToInfo
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
ppContractInfo :: ContractInfo -> Doc
ppContractInfo ci = align $ vcat
  [ ppStat "  VERIFIED"   (verified (allConds ci))
  , ppStat "UNVERIFIED" (unverified (allConds ci))
  ]
 where
  verified      = filter cVerified
  unverified    = filter (not . cVerified)
  ppStat t fs = if null fs then empty else text t <> text ":" <+> hsep (text . cName <$> fs)

allConds :: ContractInfo -> [Cond]
allConds ci = ciPreConds ci ++ ciPostConds ci

--- Adds an operation to the already processed preconditions.
addPreCondToInfo :: Cond -> ContractInfo -> ContractInfo
addPreCondToInfo c ci = ci { ciPreConds = c : ciPreConds ci }

--- Adds an operation to the already processed postconditions.
addPostCondToInfo :: Cond -> ContractInfo -> ContractInfo
addPostCondToInfo c ci = ci { ciPostConds = c : ciPostConds ci }
