{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# LANGUAGE PatternGuards #-}
{-# OPTIONS_GHC -Wno-overlapping-patterns #-}
{-# LANGUAGE DoAndIfThenElse #-}

module ProverPrototype(plugin) where

import GHC.Tc.Types (TcPlugin(..), TcPluginM, TcPluginSolver, TcPluginSolveResult (TcPluginOk), TcPluginRewriter)
import GHC.Driver.Plugins
    ( Plugin(..), defaultPlugin, CommandLineOption )
import GHC.Plugins
    ( TyCon,
      UniqFM,
      NamedThing(..),
      mkModuleName,
      fsLit,
      mkTcOcc,
      Kind,
      splitTyConApp_maybe,
      getOccFS,
      unpackFS,
      isNumLitTy,
      text,
      tyVarName, Type )
import GHC.Types.Unique.FM (emptyUFM)
import GHC.TcPluginM.Extra (tracePlugin, lookupModule, lookupName, evByFiat)
import GHC.Num (Natural, integerToNatural)
import GHC.Tc.Types.Constraint (EqCt (..), CanEqLHS (..), CtEvidence, ctPred, Ct)
import GHC.Types.Var (TcTyVar, Var (..))
import GHC.Types.Name (Name)
import GHC.Tc.Plugin (tcPluginIO, tcPluginTrace, tcLookupTyCon)
import GHC.Utils.Outputable (Outputable(..))
import GHC.Core.Predicate (Pred(..), EqRel (..), classifyPredType, getEqPredTys)
import GHC.Tc.Utils.TcType (getTyVar_maybe)
import Data.Maybe (catMaybes, mapMaybe, fromMaybe, isJust)
import GHC.Utils.Misc (ordNub)
import Data.List (intercalate, (\\))
import Description
import Data.IORef (IORef, newIORef, readIORef, writeIORef)
import System.Directory (doesFileExist)
import Data.Aeson (encodeFile)
import GHC.Data.Maybe (isNothing)
import GHC.Tc.Types.Evidence (EvTerm)

plugin :: Plugin
plugin = defaultPlugin { tcPlugin = Just . proverPlugin } -- Currently discarding the arguments.


proverPlugin ::
  [CommandLineOption] -> -- | Arguments to the plugin.
  TcPlugin
proverPlugin args = -- tracePlugin "prototype-ghc-prover"
  TcPlugin
  { tcPluginInit  = proverPluginInit args
  , tcPluginSolve = proverPluginSolver
  , tcPluginRewrite = proverPluginRewrite
  , tcPluginStop = proverPluginStop
  }

-- TODO: Unsure I still need these constructors.
data ProverState = ProverState
  { natTyCon        :: TyCon
  , knownNatTyCon   :: TyCon
  , descriptionFile :: FilePath
  -- ^ The file containing the proof tokens for the expressions.
  , proofTokens     :: IORef [ProofToken]
  }

proverPluginInit :: [CommandLineOption] -> TcPluginM ProverState
proverPluginInit args = do
  -- Load the type constructors.
  md <- lookupModule natModule natPackage
  natTcNm <- lookupName md (mkTcOcc "Nat")
  knownNatTcNm <- lookupName md (mkTcOcc "KnownNat")
  natTyC <- tcLookupTyCon natTcNm
  knatTyC <- tcLookupTyCon knownNatTcNm
  -- Load the proof tokens.
  -- TODO: Read from CLI options in a clean way.
  let path:_ = args
  -- TODO: Add some error management of sorts.
  fileExists <- tcPluginIO $ doesFileExist path
  mProofTokens <-
    if fileExists then
      tcPluginIO $ loadDescriptionFile path
    else
      return Nothing
  proofTokens <- tcPluginIO $ newIORef $ fromMaybe [] mProofTokens
  return $ ProverState natTyC knatTyC path proofTokens
  where
    natModule = mkModuleName "GHC.TypeNats"
    natPackage = fsLit "base"

proverPluginSolver :: ProverState -> TcPluginSolver
proverPluginSolver ps@(ProverState natTc knatTc _ proofTokensRef) ev given wanted =
  do
    tcPluginTrace "" $ text "Tentative Coq output:"
    let natEquations  = zip (map (ctToExpr ps) wanted) wanted
        natEqWanted   = mapMaybe fst natEquations
        ctWanted      = map snd $ filter (\(e,_) -> isJust e) natEquations
        coqWanted     = map natEqToCoq natEqWanted
        natEqCoq      = zip coqWanted natEqWanted
    -- For debugging purposes.
    -- TODO: Add a toggle.
    mapM_ (tcPluginTrace "" . text) coqWanted
    mapM_ (tcPluginTrace "" . ppr) given
    mapM_ (tcPluginTrace "" . ppr) wanted
    -- For each expression, if it's not already in the proof state, add it.
    proofTokens <- tcPluginIO $ readIORef proofTokensRef
    -- let expsWanted = coqWanted
    --     expsToAdd  = expsWanted \\ map proofExpression proofTokens
        -- tokensToAdd = map createProofTokenWithFile 
        -- tokens = proofTokens ++ tokensToAdd
    let oldExprs  = map proofExpression proofTokens
        newNatEqs = filter (\e -> fst e `notElem` oldExprs) natEqCoq
    if null newNatEqs then do
      -- If there's no new expression, we'll check out the ones that exist.
      tokens <- tcPluginIO $ mapM checkProofToken proofTokens
      tcPluginIO $ writeIORef proofTokensRef tokens
      if all isProofValid tokens then do
        -- Return the proofs with evidence.
        let evidence = map (evBy . getEqPredTys . ctPred) ctWanted
        return (TcPluginOk (zip evidence ctWanted) [])
      else
        -- If some are invalid, we don't improve the state at all.
        -- TODO: Is it useful to have better state management here since
        -- anyway we should only get one thing to prove at a time?
        return (TcPluginOk [] [])
    else do
      -- If there are new texpressions, we know that it won't work since there's
      -- no proof yet.
      -- For every new token, we have to create the associated new file.
      newTokens <- tcPluginIO $ mapM (createProofTokenWithFile . snd) natEqCoq
      let tokens = proofTokens ++ newTokens
      tcPluginIO $ writeIORef proofTokensRef tokens
      return (TcPluginOk [] [])

evBy :: (Type, Type) -> EvTerm
evBy (t1, t2) = evByFiat "External prover" t1 t2

proverPluginRewrite :: ProverState -> UniqFM TyCon TcPluginRewriter
proverPluginRewrite = const emptyUFM

-- On shutdown, the plugin will write out the definition file.
proverPluginStop :: ProverState -> TcPluginM ()
proverPluginStop ps = tcPluginIO $ do
  tokens <- readIORef (proofTokens ps)
  encodeFile (descriptionFile ps) tokens

termToExpr :: ProverState -> Kind -> Maybe NatExpression
termToExpr ps k
  -- When we stumble upon a type construction (e.g. `+`).
  | Just (tc, terms) <- splitTyConApp_maybe k =
    case tc of
      typeNatAddTyCon -> do
        let x:[y] = terms
        e1 <- termToExpr ps x
        e2 <- termToExpr ps y
        return $ NatAdd e1 e2
      typeNatMulTyCon -> do
        let x:[y] = terms
        e1 <- termToExpr ps x
        e2 <- termToExpr ps y
        return $ NatMul e1 e2
  -- A variable name.
  | Just tv <- getTyVar_maybe k =
    do
      let n = tyVarName tv
      return $ NatVar (unpackFS $ getOccFS n)
  -- A literal.
  | Just lit <- isNumLitTy k =
      return $ NatLit $ integerToNatural lit
  | otherwise = Nothing

-- | Transforms an equality into a expression on Nats.
ctToExpr :: ProverState -> Ct -> Maybe NatEq
ctToExpr ps ctEv =
  case classifyPredType (ctPred ctEv) of
    -- If it's an equality, we try to translate it.
    EqPred NomEq t1 t2 ->
      do
        e1 <- termToExpr ps t1
        e2 <- termToExpr ps t2
        return (NatEq e1 e2)
    _ -> Nothing

transformVar :: TcTyVar -> TcPluginM (Maybe NatExpression)
transformVar v =
  let ty = varType v
  in return Nothing

transformCtEq :: EqCt -> TcPluginM (Maybe NatExpression)
transformCtEq e =
  return $ case eq_lhs e of
    TyVarLHS tcV -> Nothing
    TyFamLHS tyCon [args] -> Nothing

