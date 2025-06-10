module GHC.TypeNats.Proof.Plugin.Proof
  ( Proof(..)
  , hasProof
  , tySignature
  , addTcPluginErr
  ) where

import Prelude hiding ((<>))

import Control.Monad (forM_)
import Data.Either (partitionEithers)
import Data.List (find)
import Data.Maybe (fromMaybe)
import GHC.TcPlugin.API
  ( Name, Unique, Outputable, MonadTcPlugin, SDoc, TyVar, PredType
  , ppr, tcLookupClass
  )
import GHC.TcPlugin.API.Internal (unsafeLiftTcM)
import GHC.Core (IsOrphan(..))
import GHC.Core.Class
  (Class(..), classMethods, classATs, pprFunDep, classTvsFds, classSCTheta)
import GHC.Core.TyCo.Rep (Type(..))
import GHC.Core.Type (substTy, zipTvSubst)
import GHC.Core.InstEnv
  ( InstEnvs(..), ClsInst(..), OverlapMode(..)
  , classInstances, memberInstEnv, instanceSig, overlapMode
  )
import GHC.Tc.Errors.Types (TcRnMessage(..))
import GHC.Tc.Utils.Monad (addErrAt)
import GHC.Types.Error (GhcHint(..), mkPlainError, mkSimpleUnknownDiagnostic)
import GHC.Types.Name (NamedThing(..), getSrcSpan)
import GHC.Types.SrcLoc (SrcSpan)
import GHC.Types.Unique (Uniquable(..))
import GHC.Types.Unique.Supply (MonadUnique(..))
import GHC.Utils.Outputable
  ( (<+>), ($$), (<>), bullet, nest, vcat, quotes, hsep
  )

import GHC.TypeNats.Proof.Plugin.KnownTypes
import GHC.TypeNats.Proof.Plugin.Config
import GHC.TypeNats.Proof.Plugin.Comment
import GHC.TypeNats.Proof.Plugin.Prover

-- | All data making up a proof.
data Proof = Proof
  { -- | the proof signature
    proofSignature :: Signature Tynal
  , -- | the matching proof comment
    proofComment :: ProofComment Name
  , -- | the corresponding Haskell class
    proofClass :: Class
  , -- | the corresponding Haskell instance
    proofInstance :: ClsInst
  , -- | a unique for easy data management
    proofUnique :: Unique
  }

instance Uniquable Proof where
  getUnique = proofUnique

instance Outputable Proof where
  ppr Proof{..} = ppr proofSignature

-- | Checks for the given proof comments, whether they match with a corresponsing
-- class / instance combination describing the proof signature.
hasProof ::
  MonadTcPlugin m =>
  KnownTypes -> InstEnvs -> ProofComment Name -> m (Maybe Proof)
hasProof kt ie@InstEnvs{..} proofComment@ProofComment{..} = do
  proofClass <- tcLookupClass pcName

  let classParams = dropTKVars $ classTyVars proofClass
      instances = classInstances ie proofClass
      ref = mkRef (getName $ classTyCon proofClass) classParams
      cloc = getSrcSpan proofClass

  -- check that there is are no unwanted extras
  checkForNoUnwanted ref cloc "method declarations"
     ppr getSrcSpan $ classMethods proofClass
  checkForNoUnwanted ref cloc "associated types"
     ppr getSrcSpan $ classATs proofClass
  checkForNoUnwanted ref cloc "functional dependencies"
     pprFunDep (const $ getSrcSpan proofClass) $ snd $ classTvsFds proofClass

  -- check that all instances are locally defined
  case find (not . memberInstEnv ie_local) instances of
    Nothing -> return ()
    Just inst@ClsInst{..} ->
      addTcPluginErrIns ref (getSrcSpan inst) pcLocation
        [ "Hence, instances of" <+> ref
          $$ "should be declared in the same module as the class,"
        , "but" <+> mkRef is_cls_nm is_tvs <+> "is declared at:"
          $$ nest 2 (ppr $ getSrcSpan inst)
        ] Nothing

  -- check that there is only one single instance with no unwanted extras
  case instances of
    [] -> do
      addTcPluginErrIns ref cloc pcLocation
        [ singleInstanceMsg
        , "but no such instance has been declared."
        ] Nothing
      return Nothing
    is@(i0:_:_) -> do
      addTcPluginErrIns ref (getSrcSpan i0) pcLocation
        [ singleInstanceMsg
        , "but multiple such instances have been declared:" <>
          vcat (nest 2 . ppr . getSrcSpan <$> is)
        ] Nothing
      return Nothing
    [proofInstance@ClsInst{..}] -> do
      let iloc = getSrcSpan proofInstance
          fromSig = partitionEithers . fmap (fmap specializeTerm . fromType kt)
          (noVs, sig@Signature{..}) = tySignature proofClass proofInstance
          (noWs, premise) = fromSig sigPremise
          (noGs, conclusion) = fromSig sigConclusion
          proofSignature = sig
            { sigPremise = premise
            , sigConclusion = conclusion
            }

          selectedInstanceMsg
             = "where the instance at"
            $$ nest 2 (ppr iloc)
            $$ "is considered to declare the premises of the proof."

      case overlapMode is_flag of
        NoOverlap{} -> return ()
        _ -> addTcPluginErrIns ref iloc pcLocation
               [ selectedInstanceMsg
               , "However, this instance cannot have any overlaps."
               ] $ Just
               [ "Remove any overlap pragmas from the declaration, or"
               , "disable the plugin."
               ]
      case is_orphan of
        NotOrphan{} -> return ()
        _ -> addTcPluginErrIns ref iloc pcLocation
               [ selectedInstanceMsg
               , "This instance is required to be non-orphan."
               ] Nothing

      if null noVs && null noWs && null noGs then do
        proofUnique <- unsafeLiftTcM getUniqueM
        return $ Just Proof{..}
      else do
        forM_ noVs $ \ty ->
          addTcPluginErrIns ref iloc pcLocation
            [ selectedInstanceMsg
            , "Hence, the right-hand side of the instance must match"
              $$ "with the right-hand side of the corresponding class,"
            , "but there is one instance parameter," <+>
              "which is no plain type variable:"
              $$ nest 2 (ppr ty)
            ] $ Just
            [ "Remove any class, type synonym or type family applications"
              $$ "from that parameter, or"
            , "disable the plugin."
            ]
        forM_ noWs $ addTcPluginErrTy iloc
        forM_ noGs $ addTcPluginErrTy cloc
        return Nothing
 where
  checkForNoUnwanted ::
    (Outputable a, MonadTcPlugin m) =>
    SDoc -> SrcSpan -> SDoc -> (a -> SDoc) -> (a -> SrcSpan) -> [a] -> m ()
  checkForNoUnwanted ref loc xType p gLoc = \case
    []  -> return ()
    x:_ -> addTcPluginErr loc
      [ ref <+>  "has been marked as a type-nat proof by the comment at:"
        $$ nest 2 (ppr pcLocation)
      , "Hence," <+> ref <+> "should not have any" <+> xType <> "s,"
      , "but it defines" <+> quotes (p x) <+> "at:"
        $$ nest 2 (ppr $ gLoc x)
      , "In the class declaration for" <+> ref <> "."
      ]
      [ "Make sure the proof comment refers to the right class, or"
      , "remove" <+> quotes (p x) <+> "from the class, or"
      , "disable the plugin."
      ]

  addTcPluginErrIns ::
    MonadTcPlugin m =>
    SDoc -> SrcSpan ->  SrcSpan -> [SDoc] -> Maybe [SDoc] -> m ()
  addTcPluginErrIns ref loc pcLoc msgs mhints =
    addTcPluginErr loc
      ( ( ref <+> "has been marked as a type-nat proof by the comment at:"
          $$ nest 2 (ppr pcLoc)
        ) : msgs
      )
    $ fromMaybe
        [ "Make sure the proof comment refers to the right class and"
        , "that there has been declared exactly one instance of that"
          $$ "class in the same module or"
        , "disable the plugin."
        ] mhints

  addTcPluginErrTy :: MonadTcPlugin m => SrcSpan -> Type -> m ()
  addTcPluginErrTy loc ty = addTcPluginErr loc
    [ "The following type expression is currently not supported:"
      $$ nest 2 (ppr ty)
    ] []

  singleInstanceMsg :: SDoc
  singleInstanceMsg =
       "Hence, there must be exactly one instance declaring the"
    $$ "premises of the proof, even if no premise is required,"

  mkRef :: Name -> [TyVar] -> SDoc
  mkRef name vs = quotes $ ppr name <+> hsep (ppr <$> dropTKVars vs)

-- | Turns an eligible class / instance combination into a t'Signature'.
tySignature :: Class -> ClsInst -> ([Type], Signature PredType)
tySignature sigClass sigInstance = (noTyVars, Signature{..})
 where
  cParams = dropTKVars $ classTyVars sigClass
  (_, sigPremise, _, dropTKTypes -> iParams) = instanceSig sigInstance
  sigConclusion = substTy (zipTvSubst cParams iParams) <$> classSCTheta sigClass
  (noTyVars, sigVars) = partitionEithers $ (<$> iParams) $ \case
    TyVarTy v -> Right v
    ty        -> Left ty

-- | Adds plugin specific error formatting.
addTcPluginErr :: MonadTcPlugin m => SrcSpan -> [SDoc] -> [SDoc] -> m ()
addTcPluginErr loc msgs hints
  = addErrAtTc loc (UnknownHint <$> hints)
  $ vcat $ fmap (bullet <+>)
  $ (quotes pluginName <+> "is encountering issues") : msgs

-- | Adds a new error in the 'TcPluginM' monad.
addErrAtTc :: MonadTcPlugin m => SrcSpan -> [GhcHint] -> SDoc -> m ()
addErrAtTc loc hints
  = unsafeLiftTcM
  . addErrAt loc
  . TcRnUnknownMessage
  . mkSimpleUnknownDiagnostic
  . mkPlainError hints
