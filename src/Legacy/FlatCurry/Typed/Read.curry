-----------------------------------------------------------------------------
--- Some operations to read type-annotated FlatCurry programs.
---
--- @author  Michael Hanus
--- @version October 2021
---------------------------------------------------------------------------

module Legacy.FlatCurry.Typed.Read where

import Data.IORef
import Data.List         ( find, nub )
import Data.Maybe        ( fromJust )

-- Imports from dependencies:
import FlatCurry.Annotated.Goodies

import FlatCurry.Typed.Goodies
import FlatCurry.Typed.Names
import FlatCurry.Typed.Read ( readTypedFlatCurryWithoutForall )
import FlatCurry.Typed.Simplify
import FlatCurry.Typed.Types
import Legacy.VerifierState
import PackageConfig ( packagePath )
import ToolOptions

----------------------------------------------------------------------------
--- Extract all user-defined typed FlatCurry functions that might be called
--- by a given list of functions.
getAllFunctions :: IORef VState -> [QName] -> IO [TAFuncDecl]
getAllFunctions vstref newfuns = do
  currmods <- readIORef vstref >>= return . currTAProgs
  getAllFuncs currmods [] newfuns
 where
  getAllFuncs _ currfuncs [] = return (reverse currfuncs)
  getAllFuncs currmods currfuncs (newfun:newfuncs)
    | newfun `elem` map (pre . fst) transPrimCons ++ map funcName currfuncs
      || isPrimOp newfun
    = getAllFuncs currmods currfuncs newfuncs
    | fst newfun `elem` map progName currmods
    = maybe
        (-- if we don't find the qname, it must be a constructor:
         getAllFuncs currmods currfuncs newfuncs)
        (\fdecl -> getAllFuncs currmods (fdecl : currfuncs)
                               (newfuncs ++ nub (funcsOfFuncDecl fdecl)))
        (find (\fd -> funcName fd == newfun)
              (progFuncs
                 (fromJust (find (\m -> progName m == fst newfun) currmods))))
    | otherwise -- we must load a new module
    = do let mname = fst newfun
         opts <- readVerifyInfoRef vstref >>= return . toolOpts
         printWhenStatus opts $
           "Loading module '" ++ mname ++ "' for '"++ snd newfun ++"'"
         newmod <- readTypedFlatCurryWithoutForall mname >>= return . simpProg
         modifyIORef vstref (addProgToState newmod)
         getAllFuncs (newmod : currmods) currfuncs (newfun:newfuncs)

----------------------------------------------------------------------------
