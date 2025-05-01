{-# LANGUAGE TemplateHaskellQuotes #-}
module GHC.TypeNats.Proof.Plugin.KnownTypes
  ( KOp(..)
  , KnownTypes(..)
  , FromTyCon(..)
  , lookupKnownTypes
  ) where

import GHC.Base (Constraint, Type)
import GHC.Builtin.Types (eqTyCon, naturalTyCon)
import GHC.Builtin.Types.Literals
  ( typeNatAddTyCon, typeNatSubTyCon, typeNatMulTyCon
  , typeNatExpTyCon, typeNatDivTyCon, typeNatModTyCon, typeNatLogTyCon
  )
import GHC.Core.TyCon (TyCon)
import GHC.Data.FastString (mkFastString)
import GHC.Data.IOEnv (getEnv)
import GHC.Plugins (HscEnv(..), liftIO, thNameToGhcNameIO)
import GHC.Tc.Types (Env(..), TcM)
import GHC.Tc.Utils.Env (tcLookupTyCon)
import GHC.TypeNats (Nat)
import GHC.Types.Unique.FM (listToUFM, lookupUFM)
import GHC.Utils.Outputable
  (SDoc, Outputable(..), (<+>), braces, pprWithCommas)

import qualified Data.Kind
import qualified Data.Type.Ord
import qualified GHC.TypeError
import qualified GHC.TypeLits.Extra
import qualified GHC.TypeNats.Proof

-- | The known Tynal operator.
data KOp sig where
  EqC  :: KOp (Nat -> Nat -> Constraint)
  LtC  :: KOp (Nat -> Nat -> Constraint)
  LeC  :: KOp (Nat -> Nat -> Constraint)
  GtC  :: KOp (Nat -> Nat -> Constraint)
  GeC  :: KOp (Nat -> Nat -> Constraint)
  Add  :: KOp (Nat -> Nat -> Nat)
  Sub  :: KOp (Nat -> Nat -> Nat)
  Mul  :: KOp (Nat -> Nat -> Nat)
  Exp  :: KOp (Nat -> Nat -> Nat)
  Div  :: KOp (Nat -> Nat -> Nat)
  Mod  :: KOp (Nat -> Nat -> Nat)
  Log2 :: KOp (Nat -> Nat)
  Min  :: KOp (Nat -> Nat -> Nat)
  Max  :: KOp (Nat -> Nat -> Nat)
  FLog :: KOp (Nat -> Nat -> Nat)
  CLog :: KOp (Nat -> Nat -> Nat)
  Log  :: KOp (Nat -> Nat -> Nat)
  GCD  :: KOp (Nat -> Nat -> Nat)
  LCM  :: KOp (Nat -> Nat -> Nat)

deriving stock instance Eq   (KOp sig)
deriving stock instance Ord  (KOp sig)
deriving stock instance Show (KOp sig)

instance Outputable (KOp sig) where
  ppr = ppr . mkFastString . show

type AllArgsClass :: (Type -> Constraint) -> Type -> Constraint
type family AllArgsClass c sig where
  AllArgsClass c (a -> b) = (c a, AllArgsClass c b)
  AllArgsClass c _        = ()

data KnownTypes = KnownTypes
  { -- | Data.Constraint.Dict
    ktConstraint :: TyCon
  , -- | GHC.Natural.Natural
    ktNat :: TyCon
  , -- | GHC.TypeError.Assert
    ktAssert :: TyCon
  , -- | Data.Type.Ord.OrdCond
    ktOrdCond :: TyCon
  , -- | GHC.TypeNats.Proof
    ktQED :: TyCon
  , -- | known operators
    kOp :: forall sig. KOp sig -> TyCon
  }

instance Outputable KnownTypes where
  ppr KnownTypes{..} =
    ("KnownTypes" <+>) $ braces $ ("" <+>) $ (<+> "") $ pprWithCommas id
      [ ppr ktConstraint, ppr ktNat, ppr ktAssert, ppr ktOrdCond
      , pOp EqC,  pOp LtC,  pOp LeC, pOp GtC, pOp GeC,  pOp Add, pOp Sub
      , pOp Log2, pOp Mul,  pOp Exp, pOp Log, pOp FLog, pOp Div, pOp Mod
      , pOp Min,  pOp CLog, pOp Max, pOp GCD, pOp LCM
      ]
   where
    pOp :: forall sig. KOp sig -> SDoc
    pOp = ppr . kOp

class FromTyCon a where
  fromTyCon :: KnownTypes -> TyCon -> Maybe (KOp a)

instance FromTyCon (Nat -> Nat) where
  fromTyCon KnownTypes{..} = lookupUFM $ listToUFM $ (\x -> (kOp x, x))
    <$> [ Log2 ]

instance FromTyCon (Nat -> Nat -> Constraint) where
  fromTyCon KnownTypes{..} = lookupUFM $ listToUFM $ (\x -> (kOp x, x))
    <$> [ EqC, LtC, LeC, GtC, GeC ]

instance FromTyCon (Nat -> Nat -> Nat) where
  fromTyCon KnownTypes{..} = lookupUFM $ listToUFM $ (\x -> (kOp x, x))
    <$> [ Add, Sub, Mul, Exp, Div, Mod, Min, Max
        , FLog, CLog, Log, GCD, LCM
        ]

-- | Retrieves the missing 'TyCon's that are not exposed via the GHC
-- API.
lookupKnownTypes :: TcM KnownTypes
lookupKnownTypes = do
  let ktNat = naturalTyCon
  ktConstraint <- lkup ''Data.Kind.Constraint
  ktAssert     <- lkup ''GHC.TypeError.Assert
  ktOrdCond    <- lkup ''Data.Type.Ord.OrdCond
  ktQED        <- lkup ''GHC.TypeNats.Proof.QED

  ltTyCon      <- lkup ''(Data.Type.Ord.<)
  leTyCon      <- lkup ''(Data.Type.Ord.<=)
  gtTyCon      <- lkup ''(Data.Type.Ord.>)
  geTyCon      <- lkup ''(Data.Type.Ord.>=)
  minTyCon     <- lkup ''GHC.TypeLits.Extra.Min
  maxTyCon     <- lkup ''GHC.TypeLits.Extra.Max
  logTyCon     <- lkup ''GHC.TypeLits.Extra.Log
  flogTyCon    <- lkup ''GHC.TypeLits.Extra.FLog
  clogTyCon    <- lkup ''GHC.TypeLits.Extra.CLog
  gcdTyCon     <- lkup ''GHC.TypeLits.Extra.GCD
  lcmTyCon     <- lkup ''GHC.TypeLits.Extra.LCM
  let
    kOp :: forall sig. KOp sig -> TyCon
    kOp = \case
      Add  -> typeNatAddTyCon  ;  EqC -> eqTyCon   ;  Log  -> logTyCon
      Sub  -> typeNatSubTyCon  ;  LtC -> ltTyCon   ;  FLog -> flogTyCon
      Mul  -> typeNatMulTyCon  ;  LeC -> leTyCon   ;  CLog -> clogTyCon
      Exp  -> typeNatExpTyCon  ;  GtC -> gtTyCon   ;  GCD  -> gcdTyCon
      Div  -> typeNatDivTyCon  ;  GeC -> geTyCon   ;  LCM  -> lcmTyCon
      Mod  -> typeNatModTyCon  ;  Min -> minTyCon  ;
      Log2 -> typeNatLogTyCon  ;  Max -> maxTyCon  ;

  return KnownTypes{..}
 where
  lkup th = do
    nc <- hsc_NC . env_top <$> getEnv
    res <- liftIO $ thNameToGhcNameIO nc th
    maybe (fail $ "Failed to lookup " ++ show th) tcLookupTyCon res
