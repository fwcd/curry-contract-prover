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

import Control.Monad          ( unless, when )
import Control.Monad.IO.Class ( liftIO )
import Data.IORef
import Data.List          ( elemIndex, find, init, isPrefixOf, last, maximum
                          , minimum, nub, partition, splitOn, union )
import Data.Maybe         ( catMaybes, isJust, isNothing )
import Data.Monoid        ( All (..) )
import System.Environment ( getArgs, getEnv )

-- Imports from dependencies:
import Contract.Names
import Contract.Usage                    ( checkContractUsage )
import Control.Monad.Trans.Class         ( lift )
import Control.Monad.Trans.Reader        ( ReaderT, runReaderT, ask )
import Control.Monad.Trans.State         ( StateT (..), get, put, evalStateT, execStateT, modify, withStateT, gets )
import Control.Monad.Trans.Writer        ( WriterT (..), runWriter, tell )
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
import Verification.Env                  ( VTFuncEnv, VTProgEnv, currentProg, currentFuncInfo, currentFunc, currentFuncName, currentProgFuncs, funcDeclFromEnv, typeDeclFromEnv, infoToEnv, debugToEnv, baseEnv )
import Verification.Log                  ( VLevel (..), printLog, withVLevel )
import Verification.Run                  ( runTypeAnnotatedVerification )
import Verification.Options              ( VOptions (..), defaultVOptions )
import Verification.Monad                ( VM, throwVM )
import Verification.State                ( prettyVState )
import Verification.Types                ( TVerification, Verification (..), emptyVerification )
import Verification.Update               ( VFuncUpdate (..), VTFuncUpdate, VTProgUpdate, simpleVFuncUpdate, emptyVProgUpdate, emptyVFuncUpdate )

-- Imports from package modules:
import ContractInfo             ( Cond (..), ContractInfo (..), emptyContractInfo, showContractInfo )
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
                    v | v > 2     -> VAll
                      | v > 1     -> VDebug
                      | v > 0     -> VInfo
                      | otherwise -> VNone
          vopts = defaultVOptions
                    { voModules = progs
                    , voLog     = withVLevel vlvl printLog
                    }

      if optLegacy opts
        then mapM_ (proveContracts opts') progs
        else do
          result <- runTypeAnnotatedVerification (contractProver opts) vopts
          case result of
            Left e  -> putStrLn ("Verification failed: " ++ e) >> exitWith 1
            Right s -> putStrLn $ prettyVState showContractInfo s

---------------------------------------------------------------------------

--- The contract prover as a framework verification.
contractProver :: Options -> TVerification ContractInfo
contractProver opts = emptyVerification
  { prepareProg  = prepareProgContracts
  , initFuncInfo = initFuncContracts
  , verifyFunc   = verifyFuncContracts opts
  }

--- Prepares a program's contracts.
prepareProgContracts :: VTProgEnv ContractInfo -> VM VTProgUpdate
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
initFuncContracts :: VTFuncEnv ContractInfo -> VM ContractInfo
initFuncContracts env = do
  fdecls <- currentProgFuncs env

  let name            = snd $ currentFuncName env
      funcsMatching f = filter (== f name) $ snd . funcName <$> fdecls
      mkCond          = flip Cond False

  return $ emptyContractInfo
    { ciPreConds  = mkCond <$> funcsMatching toPreCondName
    , ciPostConds = mkCond <$> funcsMatching toPostCondName
    }

--- Verifies a single function declaration by proving the contracts.
verifyFuncContracts :: Options -> VTFuncEnv ContractInfo -> VM (VTFuncUpdate ContractInfo)
verifyFuncContracts opts env = do
  allfuns  <- currentProgFuncs env

  -- TODO: We should make sure the framework has simplified the functions at
  -- this point or port over simpFuncDecl

  let checkfun   = currentFunc env
      name       = snd $ funcName checkfun
      condfuns f = filter (\fd -> snd (funcName fd) == encodeContractName (f name)) allfuns
      prefuns    = condfuns toPreCondName
      postfuns   = condfuns toPostCondName
  
  -- Verify associated pre/postcondition functions
  TransOutput info checkfun' addedfuns <-
    (\m -> runTransStateM m (TransEnv opts env) checkfun) $ do
      preConds  <- mapM verifyPreCondition  prefuns
      postConds <- mapM verifyPostCondition postfuns
      return $ ContractInfo preConds postConds
  
  return $ emptyVFuncUpdate
    { vfuUpdatedFunc = Just checkfun'
    , vfuUpdatedInfo = Just info
    , vfuAddedFuncs  = addedfuns
    }

---------------------------------------------------------------------------
-- Try to verify preconditions: If an operation `f` occurring in some
-- right-hand side has a precondition, a proof for the validity of
-- this precondition is extracted.
-- If the proof is not successful, a precondition check is added to this call.

verifyPreCondition :: TAFuncDecl -> TransM Cond
verifyPreCondition prefun = do
  env <- askFuncEnv
  checkfun <- getFunc
  debugToEnv env $ "Verifying precondition " ++ pcname ++ "..."
  (rule', All verified) <- optPreConditionInRule (funcName checkfun) (funcRule checkfun)
  modifyFunc $ updFuncRule (const rule')
  return $ Cond pcname verified
  where
    pcname = snd (funcName prefun)

optPreConditionInRule :: QName -> TARule -> TransM (TARule, All)
optPreConditionInRule _ rl@(AExternal _ _) = return (rl, mempty)
optPreConditionInRule qn@(_,fn) (ARule rty rargs rhs) = do
  let targs = zip [1..] (map snd rargs)
  st <- derivedTransState (maximum (0 : map fst rargs ++ allVars rhs) + 1) rargs
  withTransState st . runWriterT $ do
    -- compute precondition of operation:
    precondformula <- lift $ preCondExpOf qn targs
    lift $ setAssertion precondformula
    newrhs <- optPreCondInExp rhs
    return (ARule rty rargs newrhs)
 where
  -- We use the Writer monad with the All monoid to track whether all
  -- preconditions in the expression could be verified.
  optPreCondInExp :: TAExpr -> WriterT All TransM TAExpr
  optPreCondInExp exp = case exp of
    AComb ty ct (qf,tys) args ->
      if qf == ("Prelude","?") && length args == 2
        then optPreCondInExp (AOr ty (args!!0) (args!!1))
        else do
          precond <- lift getAssertion
          nargs <- mapM optPreCondInExp args
          allPreConds <- map funcName <$> lift currentProgPreConds
          if toPreCondQName qf `elem` allPreConds
            then do
              lift . debugM $ "Checking call to " ++ snd qf
              (bs,_)   <- lift $ normalizeArgs nargs
              bindexps <- lift $ mapM (binding2SMT True) bs
              precondcall <- lift $ preCondExpOf qf
                               (zip (map fst bs) (map annExpr args))
              -- TODO: select from 'bindexps' only demanded argument positions
              let title = "SMT script to verify precondition of '" ++ snd qf ++
                          "' in function '" ++ fn ++ "'"
              vartypes <- lift getVarTypes
              pcproof <- lift $
                checkImplication title vartypes
                                 precond (tConj bindexps) precondcall
              let pcvalid = isJust pcproof
              if pcvalid
                then do
                  lift . infoM $ fn ++ ": PRECONDITION OF '" ++ snd qf ++ "': VERIFIED"
                  tell (All True)
                  return $ AComb ty ct (toNoCheckQName qf, tys) nargs
                else do
                  lift . infoM $ fn ++ ": PRECOND CHECK ADDED TO '" ++ snd qf ++ "'"
                  return $ AComb ty ct (qf,tys) nargs
            else return $ AComb ty ct (qf,tys) nargs
    ACase ty ct e brs -> do
      ne <- optPreCondInExp e
      freshvar <- lift getFreshVar
      be <- lift $ binding2SMT True (freshvar,ne)
      lift $ do
        addToAssertion be
        addVarTypes [ (freshvar, annExpr ne) ]
      nbrs <- mapM (optPreCondInBranch freshvar) brs
      return $ ACase ty ct ne nbrs
    AOr ty e1 e2 -> do
      ne1 <- optPreCondInExp e1
      ne2 <- optPreCondInExp e2
      return $ AOr ty ne1 ne2
    ALet ty bs e -> do
      nes <- mapM optPreCondInExp (map snd bs)
      ne  <- optPreCondInExp e
      return $ ALet ty (zip (map fst bs) nes) ne
    AFree ty fvs e -> do
      ne <- optPreCondInExp e
      return $ AFree ty fvs ne
    ATyped ty e et -> do
      ne <- optPreCondInExp e
      return $ ATyped ty ne et
    _ -> return exp

  optPreCondInBranch dvar branch = do
    ABranch p e <- lift $ renamePatternVars branch
    lift $ addToAssertion (tEquVar dvar (pat2SMT p))
    ne <- optPreCondInExp e
    return (ABranch p ne)

-- Rename argument variables of constructor pattern
renamePatternVars :: TABranchExpr -> TransM TABranchExpr
renamePatternVars (ABranch p e) =
  if isConsPattern p
    then do
      fv <- getFreshVarIndex
      let args = map fst (patArgs p)
          minarg = minimum (0 : args)
          maxarg = maximum (0 : args)
          rnm i = if i `elem` args then i - minarg + fv else i
          nargs = map (\ (v,t) -> (rnm v,t)) (patArgs p)
      setFreshVarIndex (fv + maxarg - minarg + 1)
      addVarTypes nargs
      return $ ABranch (updPatArgs (map (\ (v,t) -> (rnm v,t))) p)
                       (rnmAllVars rnm e)
    else return $ ABranch p e

---------------------------------------------------------------------------
-- Try to verify postconditions: If an operation `f` has a postcondition,
-- a proof for the validity of the postcondition is extracted.
-- If the proof is not successful, a postcondition check is added to `f`.

verifyPostCondition :: TAFuncDecl -> TransM Cond
verifyPostCondition postfun = do
  env <- askFuncEnv
  checkfun <- getFunc
  debugToEnv env $ "Verifying postcondition " ++ pcname ++ "..."
  let (postmn,postfn) = funcName postfun
      mainfunc        = snd (funcName checkfun)
      orgqn           = (postmn, reverse (drop 5 (reverse postfn)))
  let farity = funcArity checkfun
      ftype  = funcType checkfun
      targsr = zip [1..] (argTypes ftype ++ [resultType ftype])
  bodyformula     <- extractPostConditionProofObligation
                        [1 .. farity] (farity+1) (funcRule checkfun)
  precondformula  <- preCondExpOf orgqn (init targsr)
  postcondformula <- applyFunc postfun targsr >>= pred2smt
  let title = "verify postcondition of '" ++ mainfunc ++ "'..."
  debugM $ "Trying to " ++ title
  vartypes <- getVarTypes
  pcproof <- checkImplication ("SMT script to " ++ title) vartypes
                      (tConj [precondformula, bodyformula])
                      tTrue postcondformula
  Cond pcname <$> maybe
    (do infoM $ mainfunc ++ ": POSTCOND CHECK ADDED"
        modifyFunc addPostCondition
        return False )
    (\proof -> do
        opts <- askOptions
        unless (optNoProof opts) $ liftIO $
          writeFile ("PROOF_" ++ showQNameNoDots orgqn ++ "_" ++
                    "SatisfiesPostCondition.smt") proof
        infoM $ mainfunc ++ ": POSTCONDITION VERIFIED"
        return True )
    pcproof

  where
    pcname = snd (funcName postfun)


-- Decorate the given function with a precondition check:
-- If an operation `f` has some precondition `f'pre`,
-- replace the rule `f xs = rhs` by the following rules:
--
--     f xs = checkPreCond (f'NOCHECK xs) (f'pre xs) "f" xs
--     f'NOCHECK xs = rhs
addPreCondition :: TAFuncDecl -> (TAFuncDecl, [TAFuncDecl])
addPreCondition fdecl@(AFunc qf ar vis fty rule) =
  let newrule = checkPreCondRule qf rule
  in (updFuncRule (const newrule) fdecl,
      [AFunc (toNoCheckQName qf) ar vis fty rule])
  where
    checkPreCondRule :: QName -> TARule -> TARule
    checkPreCondRule qn (ARule rty rargs _) =
      ARule rty rargs (addPreConditionCheck rty FuncCall qn rty
                        (map (\ (v,t) -> AVar t v) rargs))
    checkPreCondRule qn (AExternal _ _) = error $
      "addPreConditions: cannot add precondition to external operation '" ++
      snd qn ++ "'!"

-- Decorate the given function with a postcondition check.
addPostCondition :: TAFuncDecl -> TAFuncDecl
addPostCondition fdecl = updFuncBody (const (addPostConditionCheck fn (funcRule fdecl))) fdecl
  where fn = funcName fdecl


extractPostConditionProofObligation :: [Int] -> Int -> TARule
                                    -> TransM Term
extractPostConditionProofObligation _ _ (AExternal _ s) =
  return $ tComb ("External: " ++ s) []
extractPostConditionProofObligation args resvar
                                    (ARule ty orgargs orgexp) = do
  let exp    = rnmAllVars renameRuleVar orgexp
      rtype  = resType (length orgargs) (stripForall ty)
  derivedTransState (maximum (resvar : allVars exp) + 1)
                    ((resvar, rtype) : zip args (map snd orgargs))
                    >>= put
  binding2SMT True (resvar,exp)
 where
  maxArgResult = maximum (resvar : args)
  renameRuleVar r = maybe (r + maxArgResult + 1)
                          (args!!)
                          (elemIndex r (map fst orgargs))

  resType n te =
    if n==0
      then te
      else case te of
             FuncType _ rt -> resType (n-1) rt
             _             -> error $ "Internal errror: resType: " ++ show te

-- Fetches all preconditions in the current module.
currentProgPreConds :: TransM [TAFuncDecl]
currentProgPreConds = do
  env <- askFuncEnv
  fdecls <- liftVM $ currentProgFuncs env
  return $ filter (isPreCondName . snd . funcName) fdecls

-- Returns the precondition expression for a given operation
-- and its arguments (which are assumed to be variable indices).
-- Rename all local variables by adding the `freshvar` index to them.
preCondExpOf :: QName -> [(Int,TypeExpr)] -> TransM Term
preCondExpOf qf args = do
  env <- askFuncEnv
  maybe (return tTrue)
        (\fd -> applyFunc fd args >>= pred2smt)
        (funcDeclFromEnv env (encodeContractQName (toPreCondQName (fromNoCheckQName qf))))

-- Returns the postcondition expression for a given operation
-- and its arguments (which are assumed to be variable indices).
-- Rename all local variables by adding `freshvar` to them and
-- return the new freshvar value.
postCondExpOf :: QName -> [(Int,TypeExpr)] -> TransM Term
postCondExpOf qf args = do
  env <- askFuncEnv
  maybe (return tTrue)
        (\fd -> applyFunc fd args >>= pred2smt)
        (funcDeclFromEnv env (encodeContractQName (toPostCondQName (fromNoCheckQName qf))))

-- Applies a function declaration on a list of arguments,
-- which are assumed to be variable indices, and returns
-- the renamed body of the function declaration.
-- All local variables are renamed by adding `freshvar` to them.
-- Also the new fresh variable index is returned.
applyFunc :: TAFuncDecl -> [(Int,TypeExpr)] -> TransM TAExpr
applyFunc fdecl targs = do
  fv <- getFreshVarIndex
  let tsub = maybe (error $ "applyFunc: types\n" ++
                            show (argTypes (funcType fdecl)) ++ "\n" ++
                            show (map snd targs) ++ "\ndo not match!")
                   id
                   (matchTypes (argTypes (funcType fdecl)) (map snd targs))
      (ARule _ orgargs orgexp) = substRule tsub (funcRule fdecl)
      exp = rnmAllVars (renameRuleVar fv orgargs) orgexp
  setFreshVarIndex (max fv (maximum (0 : args ++ allVars exp) + 1))
  return $ simpExpr $ applyArgs exp (drop (length orgargs) args)
 where
  args = map fst targs
  -- renaming function for variables in original rule:
  renameRuleVar fv orgargs r = maybe (r + fv)
                                     (args!!)
                                     (elemIndex r (map fst orgargs))

  applyArgs e [] = e
  applyArgs e (v:vs) =
    -- simple hack for eta-expansion since the type annotations are not used:
    let e_v =  AComb failed FuncCall
                     (pre "apply", failed) [e, AVar failed v]
    in applyArgs e_v vs

-- Translates a Boolean FlatCurry expression into an SMT formula.
pred2smt :: TAExpr -> TransM Term
pred2smt exp = case exp of
  AVar _ i              -> return (TSVar i)
  ALit _ l              -> return (lit2SMT l)
  AComb _ ct (qf,ftype) args ->
    if qf == pre "not" && length args == 1
      then do barg <- pred2smt (head args)
              return (tNot barg)
      else do bargs <- mapM pred2smt args
              return (TComb (cons2SMT (ct /= ConsCall || not (null bargs))
                                      False qf ftype) bargs)
  _     -> error $ "Translation of some Boolean expressions into SMT " ++
                   "not yet supported:\n" ++ show (unAnnExpr exp)


-- Translates a binding between a variable (represented by its index
-- in the first component) and a FlatCurry expression (second component).
-- The FlatCurry expression is translated into an SMT formula so that
-- the binding is axiomiatized as an equation between the variable
-- and the translated expression.
-- The translated expression is normalized when necessary.
-- For this purpose, a "fresh variable index" is passed as a state.
-- Moreover, the returned state contains also the types of all fresh variables.
-- If the first argument is `False`, the expression is not strictly demanded,
-- i.e., possible contracts of it (if it is a function call) are ignored.
binding2SMT :: Bool -> (Int,TAExpr) -> TransM Term
binding2SMT odemanded (oresvar,oexp) =
  exp2smt odemanded (oresvar, simpExpr oexp)
 where
  exp2smt demanded (resvar,exp) = case exp of
    AVar _ i -> return $ if resvar==i then tTrue
                                       else tEquVar resvar (TSVar i)
    ALit _ l -> return (tEquVar resvar (lit2SMT l))
    AComb ty ct (qf,_) args ->
      if qf == pre "?" && length args == 2
        then exp2smt demanded (resvar, AOr ty (args!!0) (args!!1))
        else do
          (bs,nargs) <- normalizeArgs args
          -- TODO: select from 'bindexps' only demanded argument positions
          opts <- askOptions
          bindexps <- mapM (exp2smt (isPrimOp qf || optStrict opts)) bs
          comb2smt qf ty ct nargs bs bindexps
    ALet _ bs e -> do
      addVarTypes (map fst bs)
      bindexps <- mapM (exp2smt False) (map (\ ((i,_),ae) -> (i,ae)) bs)
      bexp <- exp2smt demanded (resvar,e)
      return (tConj (bindexps ++ [bexp]))
    AOr _ e1 e2  -> do
      bexp1 <- exp2smt demanded (resvar,e1)
      bexp2 <- exp2smt demanded (resvar,e2)
      return (tDisj [bexp1, bexp2])
    ACase _ _ e brs   -> do
      freshvar <- getFreshVar
      addVarTypes [(freshvar, annExpr e)]
      argbexp <- exp2smt demanded (freshvar,e)
      bbrs    <- mapM branch2smt (map (\b -> (freshvar,b)) brs)
      return (tConj [argbexp, tDisj bbrs])
    ATyped _ e _ -> exp2smt demanded (resvar,e)
    AFree _ _ _ -> error "Free variables not yet supported!"
   where
    comb2smt qf rtype ct nargs bs bindexps
     | qf == pre "otherwise"
       -- specific handling for the moment since the front end inserts it
       -- as the last alternative of guarded rules...
     = return (tEquVar resvar tTrue)
     | ct == ConsCall -- translate data constructor
     = return (tConj (bindexps ++
                      [tEquVar resvar
                               (TComb (cons2SMT (null nargs) False qf rtype)
                                      (map arg2smt nargs))]))
     | qf == pre "apply"
     = -- cannot translate h.o. apply: ignore it
       return tTrue
     | isPrimOp qf
     = return (tConj (bindexps ++
                      [tEquVar resvar (TComb (cons2SMT True False qf rtype)
                                             (map arg2smt nargs))]))
     | otherwise -- non-primitive operation: add contract only if demanded
     = do let targs = zip (map fst bs) (map annExpr nargs)
          precond  <- preCondExpOf qf targs
          postcond <- postCondExpOf qf (targs ++ [(resvar,rtype)])
          return
            (tConj (bindexps ++ if demanded then [precond,postcond] else []))
    
    branch2smt (cvar, (ABranch p e)) = do
      branchbexp <- exp2smt demanded (resvar,e)
      addVarTypes patvars
      return (tConj [ tEquVar cvar (pat2SMT p), branchbexp])
     where
      patvars = if isConsPattern p
                  then patArgs p
                  else []
  
    arg2smt e = case e of AVar _ i -> TSVar i
                          ALit _ l -> lit2SMT l
                          _        -> error $ "Not normalized: " ++ show e

normalizeArgs :: [TAExpr] -> TransM ([(Int,TAExpr)],[TAExpr])
normalizeArgs [] = return ([],[])
normalizeArgs (e:es) = case e of
  AVar _ i -> do (bs,nes) <- normalizeArgs es
                 return ((i,e):bs, e:nes)
  _        -> do fvar <- getFreshVar
                 addVarTypes [(fvar,annExpr e)]
                 (bs,nes) <- normalizeArgs es
                 return ((fvar,e):bs, AVar (annExpr e) fvar : nes)


unzipBranches :: [TABranchExpr] -> ([TAPattern],[TAExpr])
unzipBranches []                 = ([],[])
unzipBranches (ABranch p e : brs) = (p:xs,e:ys)
 where (xs,ys) = unzipBranches brs

---------------------------------------------------------------------------
checkImplication :: String -> [(Int,TypeExpr)]
                 -> Term -> Term -> Term -> TransM (Maybe String)
checkImplication scripttitle vartypes assertion impbindings imp = do
  opts <- askOptions
  if optVerify opts
    then checkImplicationWithSMT scripttitle vartypes
                                 assertion impbindings imp
    else return Nothing

-- Calls the SMT solver to check whether an assertion implies some
-- (pre/post) condition.
-- Returns `Nothing` if the proof was not successful, otherwise
-- the SMT script containing the proof (to obtain `unsat`) is returned.
checkImplicationWithSMT :: String -> [(Int,TypeExpr)]
                        -> Term -> Term -> Term -> TransM (Maybe String)
checkImplicationWithSMT scripttitle vartypes
                        assertion impbindings imp = do
  let allsyms = catMaybes
                  (map (\n -> maybe Nothing Just (untransOpName n))
                       (map qidName
                         (allQIdsOfTerm (tConj [assertion, impbindings, imp]))))
  unless (null allsyms) $ debugM $
    "Translating operations into SMT: " ++ unwords (map showQName allsyms)
  opts <- askOptions
  env  <- askFuncEnv
  (smtfuncs,fdecls,ndinfo) <- liftIO $ funcs2SMT opts (baseEnv env) allsyms
  smttypes <- genSMTTypes vartypes fdecls [assertion,impbindings,imp]
  let freshvar = maximum (map fst vartypes) + 1
      ([assertionC,impbindingsC,impC],newix) =
         nondetTransL ndinfo freshvar [assertion,impbindings,imp]
      smt = smttypes ++
            [ EmptyLine, smtfuncs, EmptyLine
            , Comment "Free variables:" ] ++
            map typedVar2SMT
                (vartypes ++ map toChoiceVar [freshvar .. newix-1]) ++
            [ EmptyLine
            , Comment "Boolean formula of assertion (known properties):"
            , sAssert assertionC, EmptyLine
            , Comment "Bindings of implication:"
            , sAssert impbindingsC, EmptyLine
            , Comment "Assert negated implication:"
            , sAssert (tNot impC), EmptyLine
            , Comment "check satisfiability:"
            , CheckSat
            , Comment "if unsat, we can omit this part of the contract check"
            ]
  smtstdtypes <- readInclude "Prelude.smt"
  smtchoice   <- if or (map snd ndinfo)
                   then readInclude "Prelude_Choice.smt"
                   else return ""
  let smtprelude = smtstdtypes ++ smtchoice
  callSMT $ "; " ++ scripttitle ++ "\n\n" ++ smtprelude ++ showSMT smt
 where
  readInclude f = liftIO $ getIncludePath f >>= readFile
  toChoiceVar i = (i, TCons (pre "Choice") [])

-- Computes SMT type declarations for all types occurring in the
-- variable types, function declarations, or as sorts in SMT terms.
genSMTTypes :: [(Int,TypeExpr)] -> [TAFuncDecl] -> [Term]
            -> TransM [Command]
genSMTTypes vartypes fdecls smtterms = do
  let -- all types occurring in function declarations and variable types:
      alltypes = concatMap typesOfFunc fdecls ++ map snd vartypes
      alltcons = foldr union [] (map tconsOfTypeExpr alltypes)
      -- all sorts occurring in SMT terms:
      allsorts = concatMap sortIdsOfSort (concatMap sortsOfTerm smtterms)
      (pretypes,usertypes) = partition ((== "Prelude") . fst) alltcons
      presorts = nub (filter (`notElem` (map tcons2SMT pretypes)) allsorts) ++
                 map tcons2SMT pretypes
  env <- askFuncEnv
  let udecls = map (maybe (error "Internal error: some datatype not found!") id)
                   (map (typeDeclFromEnv env) usertypes)
  return $ concatMap preludeSort2SMT presorts ++
           [ EmptyLine ] ++
           (if null udecls
              then []
              else [ Comment "User-defined datatypes:" ] ++
                   map tdecl2SMT udecls)

-- Calls the SMT solver (with a timeout of 2secs) on a given SMTLIB script.
-- Returns `Just` the SMT script if the result is `unsat`, otherwise `Nothing`.
callSMT :: String -> TransM (Maybe String)
callSMT smtinput = do
  opts <- askOptions
  debugM $ "SMT SCRIPT:\n" ++ showWithLineNums smtinput
  debugM $ "CALLING Z3..."
  (ecode,out,err) <- liftIO $ evalCmd "z3"
                             ["-smt2", "-in", "-T:" ++ show (optTimeout opts)]
                             smtinput
  when (ecode>0) $ do debugM $ "EXIT CODE: " ++ show ecode
                      liftIO $ writeFile "error.smt" smtinput
  debugM $ "RESULT:\n" ++ out
  unless (null err) $ debugM $ "ERROR:\n" ++ err
  let unsat = let ls = lines out in not (null ls) && head ls == "unsat"
  return $ if unsat
             then Just $ "; proved by: z3 -smt2 <SMTFILE>\n\n" ++ smtinput
             else Nothing

-- Translate a term w.r.t. non-determinism information by
-- adding fresh `Choice` variable arguments to non-deterministic operations.
-- The fresh variable index is passed as a state.
nondetTrans :: [(QName,Bool)] -> Int -> Term -> (Term,Int)
nondetTrans ndinfo ix trm = case trm of
  TConst _ -> (trm,ix)
  TSVar  _ -> (trm,ix)
  TComb f args -> let (targs,i1) = nondetTransL ndinfo ix args
                  in if maybe False
                              (\qn -> maybe False id (lookup qn ndinfo))
                              (untransOpName (qidName f))
                       then (TComb (addChoiceType f) (TSVar i1 : targs), i1+1)
                       else (TComb f targs, i1)
  Forall vs arg -> let (targ,ix1) = nondetTrans ndinfo ix arg
                   in (Forall vs targ, ix1)
  Exists vs arg -> let (targ,ix1) = nondetTrans ndinfo ix arg
                   in (Exists vs targ, ix1)
  ESMT.Let bs e -> let (tbt,ix1) = nondetTransL ndinfo ix (map snd bs)
                       (te,ix2)  = nondetTrans ndinfo ix1 e
                   in (ESMT.Let (zip (map fst bs) tbt) te, ix2)
 where
  addChoiceType (Id n)    = Id n
  addChoiceType (As n tp) = As n (SComb "Func" [SComb "Choice" [], tp])

nondetTransL :: [(QName,Bool)] -> Int -> [Term] -> ([Term],Int)
nondetTransL _ i [] = ([],i)
nondetTransL ndinfo i (t:ts) =
  let (t1,i1) = nondetTrans ndinfo i t
      (ts1,i2) = nondetTransL ndinfo i1 ts
  in (t1:ts1, i2)

-- Operations axiomatized by specific smt scripts (no longer necessary
-- since these scripts are now automatically generated by Curry2SMT.funcs2SMT).
-- However, for future work, it might be reasonable to cache these scripts
-- for faster contract checking.
axiomatizedOps :: [String]
axiomatizedOps = ["Prelude_null","Prelude_take","Prelude_length"]

---------------------------------------------------------------------------
-- Translate a typed variables to an SMT declaration:
typedVar2SMT :: (Int,TypeExpr) -> Command
typedVar2SMT (i,te) = DeclareVar (SV i (polytype2sort te))

-- Gets all type constructors of a type expression.
tconsOfTypeExpr :: TypeExpr -> [QName]
tconsOfTypeExpr (TVar _) = []
tconsOfTypeExpr (FuncType a b) =  union (tconsOfTypeExpr a) (tconsOfTypeExpr b)
tconsOfTypeExpr (TCons qName texps) =
  foldr union [qName] (map tconsOfTypeExpr texps)
tconsOfTypeExpr (ForallType _ te) =  tconsOfTypeExpr te

---------------------------------------------------------------------------
-- Adds a precondition check to a original call of the form
-- `AComb ty ct (qf,tys) args`.
addPreConditionCheck :: TypeExpr -> CombType -> QName -> TypeExpr -> [TAExpr]
                     -> TAExpr
addPreConditionCheck ty ct qf@(mn,fn) tys args =
  AComb ty FuncCall
    ((mn, maybe "checkPreCondNoShow" (const "checkPreCond") showdicttt),
     showDictTypeOf tt ~> ty ~> boolType ~> stringType ~> tt ~> ty)
    -- add Show dictionary argument of type tt, if possible:
    (maybe [] (:[]) showdicttt ++
    [ AComb ty ct (toNoCheckQName qf,tys) args
    , AComb boolType ct (toPreCondQName qf, pctype) args
    , string2TAFCY fn
    , tupleExpr args
    ])
 where
  argtypes   = map annExpr args
  tt         = tupleType argtypes
  pctype     = foldr FuncType boolType argtypes
  showdicttt = showDictOf tt

--- Transform a qualified name into a name of the corresponding function
--- without precondition checking by adding the suffix "'NOCHECK".
toNoCheckQName :: (String,String) -> (String,String)
toNoCheckQName (mn,fn) = (mn, fn ++ "'NOCHECK")

--- Drops a possible "'NOCHECK" suffix from a qualified name.
fromNoCheckQName :: (String,String) -> (String,String)
fromNoCheckQName (mn,fn) =
  (mn, let rf = reverse fn
       in reverse (drop (if take 8 rf == "KCEHCON'" then 8 else 0) rf))

-- Adds a postcondition check to a program rule of a given operation.
addPostConditionCheck :: QName -> TARule -> TAExpr
addPostConditionCheck _ (AExternal _ _) =
  error $ "Trying to add postcondition to external function!"
addPostConditionCheck qf@(mn,fn) (ARule _ lhs rhs) =
  AComb ty FuncCall
    ((mn, if showdictsexists then "checkPostCond" else "checkPostCondNoShow"),
     showDictTypeOf ty ~> showDictTypeOf tt
       ~> ty ~> (ty ~> boolType) ~> stringType ~> tt ~> ty)
    (-- add Show dictionary arguments of types ty and tt, if both exist:
     (if showdictsexists then catMaybes showdicts else []) ++
     [ rhs
     , AComb boolType (FuncPartCall 1) (toPostCondQName qf, ty) args
     , string2TAFCY fn
     , tupleExpr args
     ])
 where
  args = map (\ (i,t) -> AVar t i) lhs
  tt   = tupleType (map annExpr args)
  ty   = annExpr (last args)
  showdicts       = [showDictOf ty, showDictOf tt]
  showdictsexists = all isJust showdicts
 
------------------------------------------------------------------------------
-- Generate Show dictionary argument for a given type, if possible
-- (e.g., if the type is not polymorphic or functional).
showDictOf :: TypeExpr -> Maybe TAExpr
showDictOf te = case te of
  TCons qtc tes ->  do
    sd  <- typeCons2ShowDict qtc
    sds <- mapM showDictOf tes
    return $ AComb (showDictTypeOf te) (FuncPartCall 1)
                   (sd, foldr (~>) (showDictTypeOf te) (map showDictTypeOf tes))
                   sds
  _             -> Nothing
 where
  typeCons2ShowDict (mn,tc)
    | mn == "Prelude"
    = maybe Nothing (Just . pre) (preludeType2ShowDict tc)
    -- here we assume that a Show instance exists for the user-defined type
    -- safer solution: check the program for the existence of this instance
    | otherwise
    = Just (mn, "_inst#Prelude.Show#" ++ mn ++ "." ++ tc ++ "#")

  preludeType2ShowDict tc
    | tc `elem` ["Int", "Float", "Char", "Bool", "Maybe", "Either",
                 "IOError", "Ordering"]
    = Just $ "_inst#Prelude.Show#Prelude." ++ tc ++ "#"
    | tc `elem` ["[]","()"] || "(," `isPrefixOf` tc
    = Just $ "_inst#Prelude.Show#" ++ tc ++ "#"
    | otherwise
    = Nothing

-- Generate the type of the Show dictionary argument for a given type:
showDictTypeOf :: TypeExpr -> TypeExpr
showDictTypeOf te =
  FlatCurry.Typed.Build.unitType ~> TCons ("Prelude","_Dict#Show") [te]

---------------------------------------------------------------------------
-- The environment of the transformation process.
data TransEnv = TransEnv
  { teOptions :: Options
  , teFuncEnv :: VTFuncEnv ContractInfo
  }

-- The state of the transformation process contains
-- * the current assertion
-- * a fresh variable index
-- * a list of all introduced variables and their types:
-- * the main/checked function
data TransState = TransState
  { cAssertion :: Term
  , freshVar   :: Int
  , varTypes   :: [(Int,TypeExpr)]
  , func       :: TAFuncDecl
  }

-- The result of the transformation process.
data TransOutput a = TransOutput
  { toValue      :: a
  , toFunc       :: TAFuncDecl
  , toAddedFuncs :: [TAFuncDecl]
  }

makeTransState :: Int -> [(Int,TypeExpr)] -> TAFuncDecl -> TransState
makeTransState = TransState tTrue

defaultTransState :: TAFuncDecl -> TransState
defaultTransState = makeTransState 0 []

-- The type of the state monad contains the transformation state.
type TransM = StateT TransState (ReaderT TransEnv (WriterT [TAFuncDecl] VM))

-- Runs the trans state monad, returning the value, the transformed function and
-- any newly added function declarations.
runTransStateM :: TransM a -> TransEnv -> TAFuncDecl -> VM (TransOutput a)
runTransStateM m e fd = do
  ((x, ts), fs) <- runWriterT (runReaderT (runStateT m (defaultTransState fd)) e)
  return $ TransOutput x (func ts) fs

-- Lifts a verification monad action to the transformation monad.
liftVM :: VM a -> TransM a
liftVM = lift . lift . lift

-- Creates a state with the same function and updated fresh vars/types.
derivedTransState :: Int -> [(Int,TypeExpr)] -> TransM TransState
derivedTransState fv vts = do
  s <- get
  return $ makeTransState fv vts (func s)

-- Runs a subcomputation with the given state.
withTransState :: TransState -> TransM a -> TransM a
withTransState = withStateT . const

-- Logs a message at the debug level.
debugM :: String -> TransM ()
debugM msg = do
  env <- askFuncEnv
  debugToEnv env msg

-- Logs a message at the info level.
infoM :: String -> TransM ()
infoM msg = do
  env <- askFuncEnv
  infoToEnv env msg

-- Fetches the options from the environment.
askOptions :: TransM Options
askOptions = lift $ teOptions <$> ask

-- Fetches the function environment from the environment.
askFuncEnv :: TransM (VTFuncEnv ContractInfo)
askFuncEnv = lift $ teFuncEnv <$> ask

-- Fetches the current the function.
getFunc :: TransM TAFuncDecl
getFunc = gets func

-- Modifies the function.
modifyFunc :: (TAFuncDecl -> TAFuncDecl) -> TransM ()
modifyFunc f = modify $ \s -> s { func = f (func s) }

-- Updates the function.
putFunc :: TAFuncDecl -> TransM ()
putFunc = modifyFunc . const

-- Adds the given new functions.
tellFuncs :: [TAFuncDecl] -> TransM ()
tellFuncs = lift . lift . tell

-- Gets the current fresh variable index of the state.
getFreshVarIndex :: TransM Int
getFreshVarIndex = get >>= return . freshVar

-- Sets the fresh variable index in the state.
setFreshVarIndex :: Int -> TransM ()
setFreshVarIndex fvi = do
  st <- get
  put $ st { freshVar = fvi }

-- Gets a fresh variable index and increment the index in the state.
getFreshVar :: TransM Int
getFreshVar = do
  st <- get
  put $ st { freshVar = freshVar st + 1 }
  return $ freshVar st

-- Gets the variables and their types stored in the state.
getVarTypes :: TransM [(Int,TypeExpr)]
getVarTypes = get >>= return . varTypes

-- Adds variables and their types to the state.
addVarTypes :: [(Int,TypeExpr)] -> TransM ()
addVarTypes vts = do
  st <- get
  put $ st { varTypes = vts ++ varTypes st }

-- Gets the current assertion stored in the state.
getAssertion :: TransM Term
getAssertion = get >>= return . cAssertion

-- Sets the current assertion in the state.
setAssertion :: Term -> TransM ()
setAssertion formula = do
  st <- get
  put $ st { cAssertion = formula }

-- Add a formula to the current assertion in the state by conjunction.
addToAssertion :: Term -> TransM ()
addToAssertion formula = do
  st <- get
  put $ st { cAssertion = tConj [cAssertion st, formula] }

---------------------------------------------------------------------------
-- Auxiliaries:

--- Returns the path of a file provided as an argument in the `include`
--- directory of the package or, if this does not exists,
--- in the local `include` directory.
--- If both does not exist, a warning is issued.
getIncludePath :: String -> IO String
getIncludePath incfile = do
  ppinclude <- fmap (</> "include" </> incfile) getPackagePath
  exppinclude <- doesFileExist ppinclude
  if exppinclude
    then return ppinclude
    else do
      let localinclude = "include" </> incfile
      exlocalinclude <- doesFileExist localinclude
      if exlocalinclude
        then return localinclude
        else do putStrLn $
                  "Warning: '" ++ localinclude ++ "' required but not found!"
                return incfile

-- Shows a qualified name by replacing all dots by underscores.
showQNameNoDots :: QName -> String
showQNameNoDots = map (\c -> if c=='.' then '_' else c) . showQName

--- Shows a text with line numbers preceded:
showWithLineNums :: String -> String
showWithLineNums txt =
  let txtlines  = lines txt
      maxlog    = ilog (length txtlines + 1)
      showNum n = (take (maxlog - ilog n) (repeat ' ')) ++ show n ++ ": "
  in unlines . map (uncurry (++)) . zip (map showNum [1..]) $ txtlines

--- Checks whether a file exists in one of the directories on the PATH.
fileInPath :: String -> IO Bool
fileInPath file = do
  path <- getEnv "PATH"
  dirs <- return $ splitOn ":" path
  (fmap (any id)) $ mapM (doesFileExist . (</> file)) dirs

---------------------------------------------------------------------------
--- The value of `ilog n` is the floor of the logarithm
--- in the base 10 of `n`.
--- Fails if `n &lt;= 0`.
--- For positive integers, the returned value is
--- 1 less the number of digits in the decimal representation of `n`.
---
--- @param n - The argument.
--- @return the floor of the logarithm in the base 10 of `n`.
ilog :: Int -> Int
ilog n | n>0 = if n<10 then 0 else 1 + ilog (n `div` 10)
