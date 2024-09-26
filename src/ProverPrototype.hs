{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# LANGUAGE PatternGuards #-}
{-# OPTIONS_GHC -Wno-overlapping-patterns #-}
{-# LANGUAGE DoAndIfThenElse #-}
{-# LANGUAGE TemplateHaskellQuotes #-}
{-# LANGUAGE RecordWildCards #-}

module ProverPrototype(plugin) where

import GHC.Tc.Types (TcPlugin(..), TcPluginM, TcPluginSolver, TcPluginSolveResult (TcPluginOk), TcPluginRewriter, Env (..))
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
      tyVarName, Type, HscEnv (..), thNameToGhcNameIO )
import GHC.Types.Unique.FM (emptyUFM)
import GHC.TcPluginM.Extra (tracePlugin, lookupModule, lookupName, evByFiat)
import GHC.Num (Natural, integerToNatural)
import GHC.Tc.Types.Constraint (EqCt (..), CanEqLHS (..), CtEvidence, ctPred, Ct, ctEvidence, ctEvPred)
import GHC.Types.Var (TcTyVar, Var (..))
import GHC.Types.Name (Name)
import GHC.Tc.Plugin (tcPluginIO, tcPluginTrace, tcLookupTyCon, unsafeTcPluginTcM)
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
import qualified Language.Haskell.TH as TH
import GHC.Data.IOEnv (getEnv)
import qualified GHC.TypeNats
import qualified GHC.TypeError
import qualified Data.Type.Ord
import GHC.Core.TyCo.Rep (Type(..))
import GHC.Builtin.Types (cTupleTyCon, promotedTrueDataCon, promotedFalseDataCon)
import GHC.Builtin.Types.Literals (typeNatCmpTyCon)

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
  { ordCondTyCon    :: TyCon
  --   natTyCon        :: TyCon
  -- , knownNatTyCon   :: TyCon
  , assertTyCon     :: TyCon
  , descriptionFile :: FilePath
  -- ^ The file containing the proof tokens for the expressions.
  , proofTokens     :: IORef [ProofToken]
  }

proverPluginInit :: [CommandLineOption] -> TcPluginM ProverState
proverPluginInit args = do
  -- Load the type constructors.
  -- natTyC <- lookupTHName ''GHC.TypeNats.Nat >>= tcLookupTyCon
  -- kNatTyC <- lookupTHName ''GHC.TypeNats.KnownNat >>= tcLookupTyCon
  assertTyC <- lookupTHName ''GHC.TypeError.Assert >>= tcLookupTyCon
  ordCondTyC <- lookupTHName ''Data.Type.Ord.OrdCond >>= tcLookupTyCon
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
  return $ ProverState
    { ordCondTyCon = ordCondTyC
    , assertTyCon = assertTyC
    , descriptionFile = path
    , proofTokens = proofTokens
    }

-- From ghc-typelits-normalize.
lookupTHName :: TH.Name -> TcPluginM Name
lookupTHName th = do
    nc <- unsafeTcPluginTcM (hsc_NC . env_top <$> getEnv)
    res <- tcPluginIO $ thNameToGhcNameIO nc th
    maybe (fail $ "Failed to lookup " ++ show th) return res

proverPluginSolver :: ProverState -> TcPluginSolver
proverPluginSolver ps ev given wanted =
  do
    tcPluginTrace "" $ text "Tentative Coq output:"
    let proofTokensRef = proofTokens ps
        natEquations   = zip (map (ctToExpr ps) wanted) wanted
        natEqWanted    = mapMaybe fst natEquations
        ctWanted       = map snd $ filter (\(e,_) -> isJust e) natEquations
        coqWanted      = map natEqToCoq natEqWanted
        natEqCoq       = zip coqWanted natEqWanted
    -- For debugging purposes.
    -- TODO: Add a toggle.
    -- mapM_ (tcPluginTrace "" . text) coqWanted
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

-- These functions try to pattern match on type constructors. As GHC simplifies
-- expressions using the type equations before we have them, it can get pretty
-- convoluted. As an example, [`(<=)`](https://hackage.haskell.org/package/base-4.20.0.1/docs/GHC-TypeLits.html#t:-60--61-)
-- gets directly transformed to `Assert ...` and that's the type constructor
-- we'll have to deal with.
termToExpr :: ProverState -> Kind -> Maybe NatExpression
termToExpr ps@(ProverState {..}) k
  -- When we stumble upon a type family (e.g. `+`).
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
ctToExpr ps@(ProverState {..}) ctEv =
  case classifyPredType (ctEvPred $ ctEvidence ctEv) of
    -- If it's an equality, we try to translate it.
    EqPred NomEq t1 t2 -> go t1 t2
    _ -> Nothing
  where
    go (TyConApp tc xs) _
      | tc == assertTyCon
      -- , tc' == cTupleTyCon 0
      -- , [] <- ys
      , [TyConApp ordCondTc zs, _] <- xs
      , ordCondTc == ordCondTyCon
      , [_,cmp,lt,eq,gt] <- zs
      , TyConApp tcCmpNat [x,y] <- cmp
      , tcCmpNat == typeNatCmpTyCon
      , TyConApp ltTc [] <- lt
      , ltTc == promotedTrueDataCon
      , TyConApp eqTc [] <- eq
      , eqTc == promotedTrueDataCon
      , TyConApp gtTc [] <- gt
      , gtTc == promotedFalseDataCon
      = do      
        e1 <- termToExpr ps x
        e2 <- termToExpr ps y
        return (NatInEq e1 e2)
    go t1 t2 = Nothing
      -- e1 <- termToExpr ps t1
      -- e2 <- termToExpr ps t2
      -- return (NatEq e1 e2)

transformVar :: TcTyVar -> TcPluginM (Maybe NatExpression)
transformVar v =
  let ty = varType v
  in return Nothing

transformCtEq :: EqCt -> TcPluginM (Maybe NatExpression)
transformCtEq e =
  return $ case eq_lhs e of
    TyVarLHS tcV -> Nothing
    TyFamLHS tyCon [args] -> Nothing

