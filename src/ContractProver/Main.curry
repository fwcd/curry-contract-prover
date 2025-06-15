---------------------------------------------------------------------------
--- A tool to prove pre- or postconditions via an SMT solver (Z3)
--- and to remove the statically proven conditions from a program.
---
--- @author  Michael Hanus
--- @version October 2024
---------------------------------------------------------------------------

module ContractProver.Main ( main ) where

import Control.Monad               ( when, unless )
import Data.List                   ( splitOn )
import System.Environment          ( getArgs, getEnv )

-- Imports from dependencies:
import Contract.Names
import System.Directory            ( doesFileExist )
import System.FilePath             ( (</>) )
import System.Process              ( exitWith )
import Text.Pretty                 ( pPrint )
import Verification.Info           ( getFuncInfos )
import Verification.Log            ( VLevel (..), printLog, withVLevel )
import Verification.Options        ( VOptions (..), defaultVOptions, getSimplifyEnv )
import Verification.Run            ( runTypeAnnotatedVerification )
import Verification.State          ( ppVState, getProgInfos )

-- Imports from package modules:
import ContractProver.Info         ( ppContractInfo, allConds, cVerified )
import ContractProver.Options
import ContractProver.Verification ( contractProver )
import Legacy.ContractProver       ( proveContracts )
import FlatCurry.Typed.Names

------------------------------------------------------------------------

banner :: String
banner = unlines [bannerLine, bannerText, bannerLine]
 where
  bannerText = "Contract Checking/Verification Tool (Verification Framework Alpha)"
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
                    v | v > 2     -> VLevelAll
                      | v > 1     -> VLevelDebug
                      | v > 0     -> VLevelInfo
                      | otherwise -> VLevelNone
          vopts = defaultVOptions
                    { voModules       = progs
                    , voLog           = withVLevel vlvl printLog
                    , voUnaryPrimOps  = unaryPrimOps
                    , voBinaryPrimOps = binaryPrimOps
                    , voSkipPrelude   = True
                    }

      if optLegacy opts
        then mapM_ (proveContracts opts') progs
        else do
          result <- runTypeAnnotatedVerification (contractProver opts) vopts
          case result of
            Left e  -> putStrLn ("Verification failed: " ++ e) >> exitWith 1
            Right s -> do
              putStrLn . pPrint $ ppVState ppContractInfo s
              let conds   = getProgInfos s >>= getFuncInfos . snd >>= allConds . snd
                  uvconds = filter (not . cVerified) conds
              when (null uvconds) $
                if null conds
                  then putStrLn "NO CONTRACTS FOUND!"
                  else putStrLn "ALL CONTRACTS VERIFIED!"

--- Checks whether a file exists in one of the directories on the PATH.
fileInPath :: String -> IO Bool
fileInPath file = do
  path <- getEnv "PATH"
  dirs <- return $ splitOn ":" path
  (fmap (any id)) $ mapM (doesFileExist . (</> file)) dirs

---------------------------------------------------------------------------
