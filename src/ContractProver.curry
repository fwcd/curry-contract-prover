---------------------------------------------------------------------------
--- A tool to prove pre- or postconditions via an SMT solver (Z3)
--- and to remove the statically proven conditions from a program.
---
--- @author  Michael Hanus
--- @version October 2024
---------------------------------------------------------------------------
-- A few things to be done to improve contract checking:
--
-- * eta-expand pre- and postconditions (before contract checking)
--   in order to generate correct SMT formulas
---------------------------------------------------------------------------

module ContractProver where

import Control.Monad      ( unless, when )
import Data.IORef
import Data.List          ( elemIndex, find, init, isPrefixOf, last, maximum
                          , minimum, nub, partition, splitOn, union )
import Data.Maybe         ( catMaybes, isJust, isNothing )
import System.Environment ( getArgs, getEnv )

-- Imports from dependencies:
import Contract.Names
import Contract.Usage                    ( checkContractUsage )
import Control.Monad.Trans.Class         ( lift )
import Control.Monad.Trans.State         ( StateT, get, put, evalStateT )
import System.FilePath                   ( (</>) )
import FlatCurry.Files
import FlatCurry.Types
import qualified FlatCurry.Goodies as FCG
import FlatCurry.Annotated.Goodies
import FlatCurry.Annotated.Types
import FlatCurry.TypeAnnotated.Files     ( readTypeAnnotatedFlatCurry
                                         , typeAnnotatedFlatCurryFileName 
                                         , writeTypeAnnotatedFlatCurryFile )
import FlatCurry.TypeAnnotated.TypeSubst ( substRule )
import FlatCurry.ShowIntMod              ( showCurryModule )
import System.CurryPath                  ( runModuleActionQuiet )
import System.Directory                  ( doesFileExist )
import System.IOExts                     ( evalCmd )
import System.Process                    ( exitWith, system )
import Verification.Env                  ( TVFuncEnv, TVProgEnv, currentProg, currentFuncInfo, currentFunc, currentFuncName, currentProgFuncs, infoToEnv, debugToEnv )
import Verification.Log                  ( VLevel (..), printLog, withVLevel )
import Verification.Run                  ( runTypeAnnotatedVerification )
import Verification.Options              ( VOptions (..), defaultVOptions )
import Verification.Monad                ( VM, throwVM )
import Verification.Types                ( TVerification, Verification (..), emptyVerification )
import Verification.Update               ( TVFuncUpdate, TVProgUpdate, simpleVFuncUpdate, emptyVProgUpdate, emptyVFuncUpdate )

-- Imports from package modules:
import ESMT
import Curry2SMT
import FlatCurry.Typed.Build
import FlatCurry.Typed.Read
import FlatCurry.Typed.Goodies
import FlatCurry.Typed.Names
import FlatCurry.Typed.Simplify ( simpProg, simpFuncDecl, simpExpr )
import FlatCurry.Typed.Types
import Legacy.ContractProver    ( proveContracts )
import PackageConfig            ( getPackagePath )
import ToolOptions
import VerifierState

------------------------------------------------------------------------

banner :: String
banner = unlines [bannerLine, bannerText, bannerLine]
 where
  bannerText = "Contract Checking/Verification Tool (Version of 26/10/24)"
  bannerLine = take (length bannerText) (repeat '=')

---------------------------------------------------------------------------

main :: IO ()
main = do
  args <- getArgs
  (opts,progs) <- processOptions banner args
  let optname = optName opts
  if not (null optname)
    then putStrLn $ "Precondition for '" ++ optname ++ "':\n" ++
                    encodeContractName (toPreCondName optname) ++ "\n" ++
                    "Postcondition for '" ++ optname ++ "':\n" ++
                    encodeContractName (toPostCondName optname)
    else do
      when (optVerb opts > 0) $ putStrLn banner
      z3exists <- fileInPath "z3"
      unless (z3exists || not (optVerify opts)) $ putStrLn $ unlines $
        [ "WARNING: CONTRACT VERIFICATION SKIPPED:"
        , "The SMT solver Z3 is required for the verifier"
        , "but the program 'z3' is not found in the PATH!"]
      let opts' = if z3exists then opts else opts { optVerify = False }
          vlvl  = case optVerb opts of
                    v | v > 2     -> VAll
                      | v > 1     -> VInfo
                      | otherwise -> VNone
          vopts = defaultVOptions
                    { voModules = progs
                    , voLog     = withVLevel vlvl printLog
                    }

      if optLegacy opts
        then mapM_ (proveContracts opts') progs
        else do
          result <- runTypeAnnotatedVerification contractProver vopts
          case result of
            Left e  -> putStrLn ("Verification failed: " ++ e) >> exitWith 1
            Right _ -> return ()

---------------------------------------------------------------------------

-- TODO: Clean this up/move these types into modules

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

--- The contract prover as a framework verification.
contractProver :: TVerification ContractInfo
contractProver = emptyVerification
  { prepareProg  = prepareProgContracts
  , initFuncInfo = initFuncContracts
  , verifyFunc   = verifyFuncContracts
  }

--- Prepares a program's contracts.
prepareProgContracts :: TVProgEnv ContractInfo -> VM TVProgUpdate
prepareProgContracts env = do
  prog <- currentProg env

  let errs = checkContractUsage (progName prog)
             (map (\fd -> (snd (funcName fd), funcType fd)) (progFuncs prog))

  unless (null errs) $
    throwVM . unlines $ showOpError <$> errs

  return emptyVProgUpdate
  where
    showOpError (qf,err) =
      snd qf ++ " (module " ++ fst qf ++ "): " ++ err

--- Initializes the results for a function by finding all associated pre- and postconditions.
initFuncContracts :: TVFuncEnv ContractInfo -> VM ContractInfo
initFuncContracts env = do
  fdecls <- currentProgFuncs env

  let name            = snd $ currentFuncName env
      funcsMatching f = filter (== f name) $ snd . funcName <$> fdecls

  return $ emptyContractInfo
    { ciPreconds  = funcsMatching toPreCondName
    , ciPostconds = funcsMatching toPostCondName
    }

--- Verifies a single function declaration by proving the contracts.
verifyFuncContracts :: TVFuncEnv ContractInfo -> VM (TVFuncUpdate ContractInfo)
verifyFuncContracts env = do
  case snd $ currentFuncName env of
    name | isPreCondName  name -> verifyPreCondition  env
         | isPostCondName name -> verifyPostCondition env
         | otherwise           -> return emptyVFuncUpdate

---------------------------------------------------------------------------
-- Try to verify preconditions: If an operation `f` occurring in some
-- right-hand side has a precondition, a proof for the validity of
-- this precondition is extracted.
-- If the proof is not successful, a precondition check is added to this call.

verifyPreCondition :: TVFuncEnv ContractInfo -> VM (TVFuncUpdate ContractInfo)
verifyPreCondition env = do
  debugToEnv env $ "Verifying precondition " ++ name ++ "..."
  -- TODO: Implement this
  return emptyVFuncUpdate
  where
    name = snd $ currentFuncName env

---------------------------------------------------------------------------
-- Try to verify postconditions: If an operation `f` has a postcondition,
-- a proof for the validity of the postcondition is extracted.
-- If the proof is not successful, a postcondition check is added to `f`.

verifyPostCondition :: TVFuncEnv ContractInfo -> VM (TVFuncUpdate ContractInfo)
verifyPostCondition env = do
  debugToEnv env $ "Verifying postcondition " ++ name ++ "..."
  -- TODO: Implement this
  return emptyVFuncUpdate
  where
    name = snd $ currentFuncName env

---------------------------------------------------------------------------
-- Auxiliaries:

--- Checks whether a file exists in one of the directories on the PATH.
fileInPath :: String -> IO Bool
fileInPath file = do
  path <- getEnv "PATH"
  dirs <- return $ splitOn ":" path
  (fmap (any id)) $ mapM (doesFileExist . (</> file)) dirs
