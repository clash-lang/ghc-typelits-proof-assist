{- | A plugin for connecting properties over natural numbers, formulated
   via Haskell's type level naturals, with a proof assistant, to
   formally verify the correctness of the property stated.
-}
module GHC.TypeNats.Proof.Plugin (plugin) where

import Control.Applicative ((<|>))
import Control.Monad (foldM, forM_, forM,)
import Control.Monad.Trans.Class (lift)
import Control.Monad.Trans.State.Strict
  (StateT, execStateT, get, put, gets, modify)
import Data.Either (partitionEithers)
import Data.List (find)
import Data.List.NonEmpty (NonEmpty(..))
import Data.Maybe (isJust, catMaybes, mapMaybe)
import Data.Monoid (First(..))
import Data.String (IsString(..))
import GHC.Builtin.Types
  ( cTupleTyCon, cTupleDataCon, naturalTy
  , promotedTrueDataCon, promotedFalseDataCon
  )
import GHC.Builtin.Types.Literals (typeNatCmpTyCon)
import GHC.Core (Expr(..))
import GHC.Core.Coercion (mkUnivCo)
import GHC.Core.DataCon (dataConWrapId)
import GHC.Core.Opt.Monad (getModule)
import GHC.Core.Predicate (Pred(..), EqRel(..), classifyPredType)
import GHC.Core.TyCo.Rep (Type(..), TyLit(..), UnivCoProvenance (..))
import GHC.Core.TyCon (Role(..), isClassTyCon)
import GHC.Core.InstEnv (ClsInst(..), classInstances)
import GHC.Core.RoughMap (RoughMatchTc(..))
import GHC.Data.IOEnv (IORef)
import GHC.Data.FastString (FastString)
import GHC.Driver.Env (hscUpdateFlags)
import GHC.Driver.DynFlags (GeneralFlag(..), gopt_set)
import GHC.Driver.Plugins
  (Plugin(..), ParsedResult(..), CommandLineOption, defaultPlugin, purePlugin)
import GHC.Hs
  ( HsGroup(..), TyClGroup(..), TyClDecl(..), HsSigType(..), InstDecl(..)
  , ClsInstDecl(..), HsType(..), HsParsedModule(..), GhcRn, realSrcSpan
  )
import GHC.Utils.GlobalVars (global)
import GHC.Rename.Utils (warnUnusedLocalBinds)
import GHC.Stack (HasCallStack)
import GHC.Tc.Errors.Types (TcRnMessage(..))
import GHC.Tc.Plugin
  ( TcPluginM, tcPluginIO, tcLookupClass, tcLookupTyCon
  , getInstEnvs, newWanted, unsafeTcPluginTcM
  )
import GHC.Tc.Types (TcPlugin(..), TcPluginSolveResult(..), TcGblEnv(..), TcM)
import GHC.Tc.Types.TcRef (readTcRef, writeTcRef, newTcRef)
import GHC.Tc.Types.Constraint
  (Ct(..), ctLoc, ctLocSpan, mkNonCanonical, ctOrigin, ctPred)
import GHC.Tc.Types.Origin (CtOrigin(..), NakedScFlag(..), ClsInstOrQC(..))
import GHC.Tc.Types.Evidence (EvTerm(..), EvBindsVar, evId, evCast)
import GHC.Tc.Utils.Monad
  (addErrAt, newNameAt, addErrAt, mapMaybeM, failIfErrsM)
import GHC.Tc.Utils.TcType (PredType, eqType, mkTyConApp)
import GHC.Types.Id (Id)
import GHC.Types.Name
  ( Name, mkVarOccFS, getOccName, getOccFS, getName, occNameFS
  , getSrcSpan, isTyConName
  )
import GHC.Types.Name.Set (emptyFVs)
import GHC.Types.SrcLoc (SrcSpan(..), unLoc, noSrcSpan)
import GHC.Types.Unique.FM
  (UniqFM, emptyUFM, lookupUFM, addToUFM, nonDetEltsUFM, minusUFM, listToUFM)
import GHC.Unit.Types (GenModule(..))
import GHC.Utils.Panic (sorryDoc)
import GHC.Utils.Outputable (SDoc, (<+>), ($$), quotes, ppr, vcat, nest)
import Language.Haskell.Syntax.Decls (StandaloneKindSig(..))
import Language.Haskell.Syntax.Module.Name (moduleNameSlashes)
import System.Directory (createDirectoryIfMissing)
import System.Exit (exitFailure)
import System.FilePath ((</>))

import qualified GHC.Utils.Outputable as Doc ((<>))
import qualified Data.Map as Map (fromList, lookup)

import GHC.TypeNats.Proof.Plugin.KnownTypes
import GHC.TypeNats.Proof.Plugin.Config
import GHC.TypeNats.Proof.Plugin.Comment
import GHC.TypeNats.Proof.Plugin.Proof
import GHC.TypeNats.Proof.Plugin.Prover

-- | Some data to be shared between the different plugin phases.
type PhaseShare = Either
  [ProofComment FastString]
  (KnownTypes, [ProofComment Name])

-- | An IO reference of the shared data.
type PhaseShareRef = IORef PhaseShare

-- | The main GHC plugin.
plugin :: Plugin
plugin = defaultPlugin
  { pluginRecompile = purePlugin
  , driverPlugin = const $
      -- to keep the comments in the stream
      return . hscUpdateFlags (`gopt_set` Opt_KeepRawTokenStream)
  , parsedResultAction = \_ _ ParsedResult{..} -> do
      writeTcRef gref
        $ Left $ getProofComments $ hpm_module parsedResultModule
      return ParsedResult{..}
  , renamedResultAction = checkProofComments gref
  , tcPlugin = \opts -> Just $ TcPlugin
      { -- although the documentation claims a different behavior,
        -- this action is executed before the `renameResultAction`,
        -- which is why we cannot get the data from the `gref` yet
        tcPluginInit = case optionsParser opts of
          Left errs -> do
            forM_ errs $ \err ->
              addTcPluginErr noSrcSpan
                [ "Unknown plugin command line option:"
                  $$ nest 2 (quotes $ fromString err)
                ]
                [ "Supported options are:"
                  $$ nest 2
                    ( vcat
                        [ autoProveFlag    Doc.<> "=<Bool>"
                        , verifyProofsFlag Doc.<> "=<Bool>"
                        , proofDirFlag     Doc.<> "=<FilePath>"
                        ]
                    )
                ]
            unsafeTcPluginTcM failIfErrsM
            tcPluginIO exitFailure
          Right cfg -> do
            pref <- tcPluginIO $ newTcRef Nothing
            return (cfg, pref, gref)
      , tcPluginSolve = \(cfg, pref, sref) env gs ws -> do
          -- skip the simplification phase
          if null ws then return $ TcPluginOk [] []
          else do
            (kt, proofs) <- tcPluginIO (readTcRef pref) >>= \case
              Just x  -> return x
              Nothing -> tcPluginIO (readTcRef sref) >>= \case
                Left _ -> noShare
                Right (kt, proofComments) -> do
                  ie <- getInstEnvs
                  -- check for matching class and instance declaration
                  -- providing the signature of the proof
                  proofs <- mapMaybeM (hasProof kt ie) proofComments
                  -- fail, if errors have been encountered
                  unsafeTcPluginTcM failIfErrsM
                  -- otherwise store the result to be re-used
                  tcPluginIO $ writeTcRef pref $ Just (kt, proofs)
                  return (kt, proofs)
            pluginSolve cfg kt proofs env gs ws
      , tcPluginRewrite = const emptyUFM
      , tcPluginStop = const $ return ()
      }
  }
 where
  -- there is no other way supported by GHC to pass plugin specific
  -- data between different phases.
  gref :: PhaseShareRef
  gref = global $ Left []
  {-# NOINLINE gref #-}

-- | Preliminary proof comment checks.
checkProofComments ::
  HasCallStack =>
  PhaseShareRef ->
  [CommandLineOption] ->
  TcGblEnv ->
  HsGroup GhcRn ->
  TcM (TcGblEnv, HsGroup GhcRn)
checkProofComments gref _ gblEnv hsGroup@HsGroup{..} = do
  knownTypes <- lookupKnownTypes
  ufm <- readTcRef gref >>= foldM checkedAdd emptyUFM . either id noShare
  let fpcs = filteredProofComments ufm knownTypes
  writeTcRef gref $ Right (knownTypes, fpcs)
  unused <- forM (noMatchingClassProofComments ufm fpcs)
    $ \ProofComment{..} -> newNameAt (mkVarOccFS pcName) pcLocation
  warnUnusedLocalBinds unused emptyFVs
  return (gblEnv, hsGroup)
 where
  checkedAdd ufm pc = case lookupUFM ufm (pcName pc) of
    Nothing -> return $ addToUFM ufm (pcName pc) pc
    Just pc' -> do
      let fs = mappend "Proof (..): " $ pcName pc
      n <- newNameAt (mkVarOccFS $ pcName pc) $ pcLocation pc
      n' <- newNameAt (mkVarOccFS $ pcName pc') $ pcLocation pc'
      m <- newNameAt (mkVarOccFS fs) $ pcLocation pc
      addErrAt (pcLocation pc)
        $ TcRnDuplicateDecls (getOccName m)
        $ n' :| [n]
      return ufm

  filteredProofComments ufm knownTypes = (`mapMaybe` hs_tyclds) $ \case
    TyClGroup{..}
      | -- check that there is a matching class name
        [ClassDecl{..}] <- unLoc <$> group_tyclds
      , let pcName' = unLoc tcdLName
      , Just ProofComment{..} <- lookupUFM ufm $ occNameFS $ getOccName pcName'
      -> do -- we need to rule out classes having an explicit kind
            -- signature which does not result in a `Constraint`,
            -- because the plugin will run into an internal GHC error
            -- during the type checking phase before being able to
            -- report his type mismatch otherwise
            forM_ (unLoc <$> group_kisigs) $ \case
              StandaloneKindSig _ _ lsig
                | HsSig{..} <- unLoc lsig
                , False <- hasConstraintResult $ unLoc sig_body
                -> Nothing
              _ -> Just ()

            -- we also need to check for the existence of at least one
            -- instance with the same name at this point, as otherwise
            -- the type checking phase may never be executed, keeping a
            -- missing instance potentially undetected
            getFirst $ mconcat $ (<$> group_instds) $ (. unLoc) $ First . \case
              ClsInstD{..}
                | ClsInstDecl{..} <- cid_inst
                , HsSig{..} <- unLoc cid_poly_ty
                , Just iname <- getInstName $ unLoc sig_body
                , getOccFS iname == pcName
                -> Just ()
              _ -> Nothing

            return ProofComment { pcName = pcName', .. }
      | otherwise -> Nothing
   where
    hasConstraintResult = \case
      HsForAllTy{..}   -> hasConstraintResult $ unLoc hst_body
      HsQualTy{..}     -> hasConstraintResult $ unLoc hst_body
      HsParTy _ ty     -> hasConstraintResult $ unLoc ty
      HsKindSig _ ty _ -> hasConstraintResult $ unLoc ty
      HsBangTy _ _ ty  -> hasConstraintResult $ unLoc ty
      HsFunTy _ _ _ ty -> hasConstraintResult $ unLoc ty
      HsAppTy _ ty _   -> hasConstraintResult $ unLoc ty
      HsTyVar _ _ n    -> unLoc n == getName (ktConstraint knownTypes)
      _                -> False

    getInstName = \case
      HsForAllTy{..}   -> getInstName $ unLoc hst_body
      HsQualTy{..}     -> getInstName $ unLoc hst_body
      HsParTy _ ty     -> getInstName $ unLoc ty
      HsKindSig _ ty _ -> getInstName $ unLoc ty
      HsBangTy _ _ ty  -> getInstName $ unLoc ty
      HsAppTy _ ty _   -> getInstName $ unLoc ty
      HsTyVar _ _ n    -> return $ getName $ unLoc n
      _                -> Nothing

  noMatchingClassProofComments ufm fpcs =
    nonDetEltsUFM $ minusUFM ufm $ listToUFM $ (<$> fpcs) $ \pc ->
      let pcName' = getOccFS $ pcName pc
       in (pcName', pc { pcName = pcName' })

-- | The type check plugin.
pluginSolve ::
  HasCallStack =>
  PluginConfig ->
  KnownTypes ->
  [Proof] ->
  EvBindsVar ->
  [Ct] ->
  [Ct] ->
  TcPluginM TcPluginSolveResult
pluginSolve PluginConfig{..} kt@KnownTypes{..} proofs _ev givens wanteds = do
  Module{..} <- unsafeTcPluginTcM getModule
  -- every proof should produce a wanted (assuming that GHC cannot
  -- prove them on it's own). We only can identify these wanteds via
  -- the source location of the matching instances, as no other
  -- reference currently is shipped with the wanted. We use a
  -- classical set figure out the matching instance.
  let sspan p = (realSrcSpan $ getSrcSpan $ proofInstance p, p)
      locM = Map.fromList $ sspan <$> proofs
      (proofWs, noProofWs) = partitionEithers $ (<$> wanteds) $ \ct ->
        case ctLocSpan (ctLoc ct) `Map.lookup` locM of
          Just p | ScOrigin IsClsInst NakedSc <- ctOrigin ct -> Left (p, ct)
          _ -> Right ct
  -- We only solve the wanteds that have matching proof comments at
  -- first, as GHC may already be able to solve the other ones with
  -- the newly acquired evidence without further support. Otherwise,
  -- GHC will provide them again in next iteration, in which case
  -- `proofWs` has changed in terms of the embodied requirements.
  if not (null proofWs) then do
    evs <- (`mapMaybeM` proofWs) $ \(Proof{..}, ct) -> do
      let ProofComment{..} = proofComment
          dir = proofDir </> show pcProver </> moduleNameSlashes moduleName
      result <- tcPluginIO $
        if verifyProofs then do
          createDirectoryIfMissing True dir
          verify pcProver dir pcPreamble proofSignature pcProof
        else
          return Nothing
      case result of
        -- the proof has passed verification
        Nothing -> return $ addEvidence ct
        -- an error occurred
        Just (err :: String) -> do
          addTcPluginErr pcLocation
            [ "Verification of the" <+>
              quotes (ppr pcProver) <+> "proof failed:"
              $$ ""
              $$ vcat (fromString <$> lines err)
            ] []
          return Nothing

    -- fail, if errors have been encountered
    unsafeTcPluginTcM failIfErrsM
    -- otherwise return the new evidence
    return $ TcPluginOk evs []
  else if autoProve then do

    -- get the proof signatures from the QED class instances in scope
    ie <- getInstEnvs
    qedInstances <- classInstances ie <$> tcLookupClass (getName ktQED)
    proofSigs <- (`mapMaybeM` qedInstances) $ \case
      ClsInst{..} | [_, RM_KnownTc name] <- is_tcs, isTyConName name -> do
        tc <- tcLookupTyCon name
        if isClassTyCon tc then do
          cls <- tcLookupClass name
          case classInstances ie cls of
            [inst]
              | ([], sig) <- tySignature cls inst
              -> return $ Just sig
            _ -> return Nothing
        else
          return Nothing
      _ -> return Nothing

    -- check for proven goals that match with the given wanteds and
    -- deduce new wanteds from the premises of the successful matches.
    matches <- (`mapMaybeM` noProofWs) $ \ct ->
      case mapMaybe (proofMatch kt givens ct) proofSigs of
        []  -> return Nothing
        [x] -> return $ Just x
        xs -> do
         addTcPluginErr (RealSrcSpan (ctLocSpan (ctLoc ct)) mempty)
           [ "Automatic proof application is ambiguous."
           , "Multiple proofs in scope:"
             $$ nest 2 (vcat (ppr . snd . snd <$> xs))
             $$ "are applicable to the required wanted:"
             $$ nest 2 (pprCt kt ct)
           ]
           [ "Explicitly select one of the proofs above via"
             $$ "the methods provided by the" <+> quotes "QED" <+> "class, or"
           , "disable automatic proof application via the"
             $$ nest 2 (quotes (autoProveFlag Doc.<> "=False"))
             $$ "command line option of the plugin."
           ]
         return Nothing

    nws <- fmap concat $
      forM matches $ \((_, ct), (tys, _)) ->
        forM tys $ fmap mkNonCanonical . newWanted (ctLoc ct)

    return $ TcPluginOk (fst <$> matches) nws
  else
    return $ TcPluginOk [] []

type Binding = UniqFM Id Type
type MB a = StateT Binding Maybe a

-- | A very much incomplete attempt to deduce a wanted from a known
-- proof and the provided givens. This method may fail even though it
-- may be possible to deduce the wanted via the given artifacts.
proofMatch ::
  KnownTypes ->
  [Ct] ->
  Ct ->
  Signature PredType ->
  Maybe ((EvTerm, Ct), ([PredType], Signature PredType))
proofMatch KnownTypes{..} givens wanted sig@Signature{..} = do
  -- pick the first conclusion of the signature that matches with the
  -- wanted
  binding <- getFirst $ mconcat
    [ First $ execStateT (ctMatch wanted conclusion) emptyUFM
    | conclusion <- sigConclusion
    ]
  -- check that for each premise of the signature there is a matching given
  foldM refine [binding] sigPremise >>= \case
    -- if successful, then we can reduce the wanted to the refined
    -- premises of the signature.
    s:_  | all (isJust . lookupUFM s) sigVars ->
      ( , (apply s <$> sigPremise, sig)) <$> addEvidence wanted
    _ -> Nothing

 where
  refine :: [Binding] -> PredType -> Maybe [Binding]
  refine bindings premise =
    let xs = catMaybes
           [ execStateT (ctMatch given $ apply binding premise) binding
           | given <- givens
           , binding <- bindings
           ]
     in if null xs then Nothing else Just xs

  apply :: Binding -> Type -> Type
  apply binding = \case
    TyVarTy v -> case lookupUFM binding v of
      Just ty -> ty
      _ -> TyVarTy v
    AppTy t0 t1 -> AppTy (apply binding t0) (apply binding t1)
    TyConApp tc xs -> TyConApp tc $ apply binding <$> xs
    ty -> ty

  ctMatch :: Ct -> Type -> MB ()
  ctMatch ct ty = case classifyPredType $ ctPred ct of
    EqPred NomEq wty0 wty1
      | TyConApp tcEq tys <- ty
      , [ty0, ty1] <- dropTKTypes tys
      , tcEq == kOp EqC
      -> get >>= \s ->
           let s0 = put s >> (wty0 `matches` ty0) >> (wty1 `matches` ty1)
               s1 = put s >> (wty0 `matches` ty1) >> (wty1 `matches` ty0)
            in s0 <|> s1
    IrredPred wty -> wty `matches` ty
    _ -> mismatch

  matches :: Type -> Type -> MB ()

  matches (LitTy (NumTyLit i)) (LitTy (NumTyLit i'))
    | i == i'
    = match

  matches wty (TyVarTy v) = gets (`lookupUFM` v) >>= \case
    Nothing -> modify (\ufm -> addToUFM ufm v wty) >> match
    Just ty | eqType wty ty -> match
    _ -> mismatch

  matches (TyConApp tcAssert wtys) (TyConApp tcOp tys)
    | tcAssert == ktAssert
    , tcOp `elem` [kOp LeC, kOp LtC, kOp GeC, kOp GtC]
    , [wty, _] <- dropTKTypes wtys
    , [ty0, ty1] <- dropTKTypes tys
    , TyConApp tcOrdCond otys <- wty
    , [cmp, lt, eq, gt] <- dropTKTypes otys
    , tcOrdCond == ktOrdCond
    , TyConApp tcCmpNat ctys <- cmp
    , [wty0, wty1] <- dropTKTypes ctys
    , tcCmpNat == typeNatCmpTyCon
    , TyConApp tcLt ltys <- lt
    , [] <- dropTKTypes ltys
    , TyConApp tcEq etys <- eq
    , [] <- dropTKTypes etys
    , TyConApp tcGt gtys <- gt
    , [] <- dropTKTypes gtys
    , let pT = promotedTrueDataCon
          pF = promotedFalseDataCon
    , (tcOp, tcLt, tcEq, tcGt) `elem`
         [ (kOp LtC, pT, pF, pF)
         , (kOp LeC, pT, pT, pF)
         , (kOp GtC, pF, pF, pT)
         , (kOp GeC, pF, pT, pT)
         ]
    = (wty0 `matches` ty0) >> (wty1 `matches` ty1)

  matches (TyConApp wtc wts) (TyConApp tc ts)
    | wtc == tc
    , length wts == length ts
    = mapM_ (uncurry matches) $ zip wts ts

  matches (AppTy wty0 wty1) (AppTy ty0 ty1)
    = (wty0 `matches` ty0) >> (wty1 `matches` ty1)

  matches (FunTy waf wmult warg wres) (FunTy af mult arg res)
    | waf == af
    = (wmult `matches` mult)
    >> (warg `matches` arg)
    >> (wres `matches` res)

  matches _ _ = mismatch

  match, mismatch :: MB ()
  match    = return ()
  mismatch = lift Nothing

-- | Add evidence to the given 'Ct'.
addEvidence :: Ct -> Maybe (EvTerm, Ct)
addEvidence ct = ( , ct) <$> case classifyPredType $ ctPred ct of
  EqPred NomEq ty0 ty1
    -> return $ EvExpr $ Coercion $ mkUnivCoP Nominal ty0 ty1
  IrredPred ty1
    -> let ty0 = mkTyConApp (cTupleTyCon 0) []
           dcApp = evId $ dataConWrapId $ cTupleDataCon 0
        in return $ evCast dcApp $ mkUnivCoP Representational ty0 ty1
  _ -> Nothing
 where
  mkUnivCoP = mkUnivCo $ PluginProv pluginName

-- | Some alternative 'Ct' pretty printer.
pprCt :: HasCallStack => KnownTypes -> Ct -> SDoc
pprCt KnownTypes{..} ct = case classifyPredType $ ctPred ct of
  EqPred _ ty0 ty1 -> ppr $ TyConApp (kOp EqC) $ niceTy <$> [ty0, ty1]
  IrredPred ty -> ppr $ niceTy ty
  _ -> ppr ct
 where
  niceTy = \case
    AppTy ty ty' -> AppTy (niceTy ty) (niceTy ty')
    TyConApp tcAssert [ty, _]
      | tcAssert == ktAssert
      , TyConApp tcOrdCond tys <- ty
      , [cmp, lt, eq, gt] <- dropTKTypes tys
      , tcOrdCond == ktOrdCond
      , TyConApp tcCmpNat [ty0, ty1] <- cmp
      , tcCmpNat == typeNatCmpTyCon
      , TyConApp tcLt [] <- lt
      , TyConApp tcEq [] <- eq
      , TyConApp tcGt [] <- gt
      , let pT = promotedTrueDataCon
            pF = promotedFalseDataCon
      , Just op <- fst <$> find ((== (tcLt, tcEq, tcGt)) . snd)
           [ (LtC, (pT, pF, pF))
           , (LeC, (pT, pT, pF))
           , (GtC, (pF, pF, pT))
           , (GeC, (pF, pT, pT))
           ]
      -> TyConApp (kOp op) [naturalTy, ty0, ty1]
    TyConApp tc xs -> TyConApp tc $ niceTy <$> xs
    ForAllTy b ty -> ForAllTy b $ niceTy ty
    FunTy af mult arg res -> FunTy af mult (niceTy arg) (niceTy res)
    CastTy ty coe -> CastTy (niceTy ty) coe
    ty -> ty

-- | An escape hatch for the case that passing the global
-- 'PhaseShareRef' did not succeed (should never happen).
noShare :: HasCallStack => a
noShare = sorryDoc pluginName "no share"
