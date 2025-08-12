{-# LANGUAGE TemplateHaskellQuotes #-}
module GHC.TypeNats.Proof.Plugin.KnownTypes
  ( type (~>)(..)
  , KnownTypes(..)
  , FromTyCon(..)
  , lookupKnownTypes
  ) where

import GHC.Base (Constraint, Type)
import GHC.Builtin.Types (eqTyCon)
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

import qualified Data.Type.Bool
import qualified Data.Type.Equality
import qualified Data.Type.Ord
import qualified GHC.TypeError
import qualified GHC.TypeLits.Extra
import qualified GHC.TypeNats.Proof

-- | The known Tynal operators.
infixr ~>
data a ~> b where
  NZero :: Nat ~> Constraint
  EqC   :: a ~> a ~> Constraint
  LtC   :: Nat ~> Nat ~> Constraint
  LeC   :: Nat ~> Nat ~> Constraint
  GtC   :: Nat ~> Nat ~> Constraint
  GeC   :: Nat ~> Nat ~> Constraint
  EqB   :: a ~> a ~> Bool
  LtB   :: Nat ~> Nat ~> Bool
  LeB   :: Nat ~> Nat ~> Bool
  GtB   :: Nat ~> Nat ~> Bool
  GeB   :: Nat ~> Nat ~> Bool
  And   :: Bool ~> Bool ~> Bool
  Or    :: Bool ~> Bool ~> Bool
  Not   :: Bool ~> Bool
  If    :: Bool ~> a ~> a ~> a
  Add   :: Nat ~> Nat ~> Nat
  Sub   :: Nat ~> Nat ~> Nat
  Mul   :: Nat ~> Nat ~> Nat
  Exp   :: Nat ~> Nat ~> Nat
  Div   :: Nat ~> Nat ~> Nat
  Mod   :: Nat ~> Nat ~> Nat
  Log2  :: Nat ~> Nat
  CLog2 :: Nat ~> Nat
  FLog2 :: Nat ~> Nat
  Min   :: Nat ~> Nat ~> Nat
  Max   :: Nat ~> Nat ~> Nat
  Log   :: Nat ~> Nat ~> Nat
  FLog  :: Nat ~> Nat ~> Nat
  CLog  :: Nat ~> Nat ~> Nat
  GCD   :: Nat ~> Nat ~> Nat
  LCM   :: Nat ~> Nat ~> Nat

deriving stock instance Eq   (a ~> b)
deriving stock instance Ord  (a ~> b)
deriving stock instance Show (a ~> b)

instance Outputable (a ~> b) where
  ppr = ppr . mkFastString . show

type AllArgsClass :: (Type -> Constraint) -> Type -> Constraint
type family AllArgsClass c sig where
  AllArgsClass c (a -> b) = (c a, AllArgsClass c b)
  AllArgsClass c _        = ()

data KnownTypes = KnownTypes
  { -- | GHC.TypeError.Assert
    ktAssert :: TyCon
  , -- | Data.Type.Ord.OrdCond
    ktOrdCond :: TyCon
  , -- | GHC.TypeNats.Proof
    ktQED :: TyCon
  , -- | known operators
    kOp :: forall a b. (a ~> b) -> TyCon
  }

instance Outputable KnownTypes where
  ppr KnownTypes{..} =
    ("KnownTypes" <+>) $ braces $ ("" <+>) $ (<+> "") $ pprWithCommas id
      [ ppr ktAssert, ppr ktOrdCond, pOp EqC,  pOp LtC,   pOp LeC,  pOp GtC
      , pOp GeC, pOp EqB, pOp LtB,   pOp LeB,  pOp GtB,   pOp GeB,  pOp NZero
      , pOp And, pOp Or,  pOp Not,   pOp If,   pOp Add,   pOp Sub,  pOp Log2
      , pOp Div, pOp Mod, pOp Mul,   pOp Exp,  pOp Min,   pOp Max,  pOp Log
      , pOp GCD, pOp LCM, pOp FLog,  pOp CLog, pOp FLog2, pOp CLog2
      ]
   where
    pOp :: forall a b. (a ~> b) -> SDoc
    pOp = ppr . kOp

class FromTyCon a where
  fromTyCon :: KnownTypes -> TyCon -> Maybe a

instance FromTyCon (Nat ~> Constraint) where
  fromTyCon KnownTypes{..} = lookupUFM $ listToUFM $ (\x -> (kOp x, x))
    <$> [ NZero ]

instance FromTyCon (Bool ~> Bool ~> Constraint) where
  fromTyCon KnownTypes{..} = lookupUFM $ listToUFM $ (\x -> (kOp x, x))
    <$> [ EqC ]

instance FromTyCon (Nat ~> Nat ~> Constraint) where
  fromTyCon KnownTypes{..} = lookupUFM $ listToUFM $ (\x -> (kOp x, x))
    <$> [ EqC, LtC, LeC, GtC, GeC ]

instance FromTyCon (Nat ~> Nat ~> Bool) where
  fromTyCon KnownTypes{..} = lookupUFM $ listToUFM $ (\x -> (kOp x, x))
    <$> [ EqB, LtB, LeB, GtB, GeB ]

instance FromTyCon (Bool ~> Bool) where
  fromTyCon KnownTypes{..} = lookupUFM $ listToUFM $ (\x -> (kOp x, x))
    <$> [ Not ]

instance FromTyCon (Bool ~> Bool ~> Bool) where
  fromTyCon KnownTypes{..} = lookupUFM $ listToUFM $ (\x -> (kOp x, x))
    <$> [ EqB, And, Or ]

instance FromTyCon (Bool ~> a ~> a ~> a) where
  fromTyCon KnownTypes{..} = lookupUFM $ listToUFM $ (\x -> (kOp x, x))
    <$> [ If ]

instance FromTyCon (Nat ~> Nat) where
  fromTyCon KnownTypes{..} = lookupUFM $ listToUFM $ (\x -> (kOp x, x))
    <$> [ Log2, CLog2, FLog2 ]

instance FromTyCon (Nat ~> Nat ~> Nat) where
  fromTyCon KnownTypes{..} = lookupUFM $ listToUFM $ (\x -> (kOp x, x))
    <$> [ Add, Sub, Mul, Exp, Div, Mod, Min, Max
        , FLog, CLog, Log, GCD, LCM
        ]

-- | Retrieves the missing 'TyCon's that are not exposed via the GHC API.
lookupKnownTypes :: TcM KnownTypes
lookupKnownTypes = do
  ktAssert     <- lkup ''GHC.TypeError.Assert
  ktOrdCond    <- lkup ''Data.Type.Ord.OrdCond
  ktQED        <- lkup ''GHC.TypeNats.Proof.QED
  nZeroTyCon   <- lkup ''GHC.TypeNats.Proof.NonZero

  ltCTyCon     <- lkup ''(Data.Type.Ord.<)
  leCTyCon     <- lkup ''(Data.Type.Ord.<=)
  gtCTyCon     <- lkup ''(Data.Type.Ord.>)
  geCTyCon     <- lkup ''(Data.Type.Ord.>=)

  eqBTyCon     <- lkup ''(Data.Type.Equality.==)
  ltBTyCon     <- lkup ''(Data.Type.Ord.<?)
  leBTyCon     <- lkup ''(Data.Type.Ord.<=?)
  gtBTyCon     <- lkup ''(Data.Type.Ord.>?)
  geBTyCon     <- lkup ''(Data.Type.Ord.>=?)

  ifTyCon      <- lkup ''Data.Type.Bool.If
  notTyCon     <- lkup ''Data.Type.Bool.Not
  andTyCon     <- lkup ''(Data.Type.Bool.&&)
  orTyCon      <- lkup ''(Data.Type.Bool.||)

  minTyCon     <- lkup ''GHC.TypeLits.Extra.Min
  maxTyCon     <- lkup ''GHC.TypeLits.Extra.Max
  logTyCon     <- lkup ''GHC.TypeLits.Extra.Log
  flogTyCon    <- lkup ''GHC.TypeLits.Extra.FLog
  clogTyCon    <- lkup ''GHC.TypeLits.Extra.CLog
  gcdTyCon     <- lkup ''GHC.TypeLits.Extra.GCD
  lcmTyCon     <- lkup ''GHC.TypeLits.Extra.LCM
  clog2TyCon   <- lkup ''GHC.TypeNats.Proof.CLog2
  flog2TyCon   <- lkup ''GHC.TypeNats.Proof.FLog2
  let
    kOp :: forall a b. a ~> b -> TyCon
    kOp = \case
      Add  -> typeNatAddTyCon  ;  EqC -> eqTyCon   ;  NZero -> nZeroTyCon
      Sub  -> typeNatSubTyCon  ;  LtC -> ltCTyCon  ;  LCM   -> lcmTyCon
      Mul  -> typeNatMulTyCon  ;  LeC -> leCTyCon  ;  GCD   -> gcdTyCon
      Exp  -> typeNatExpTyCon  ;  GtC -> gtCTyCon  ;  CLog  -> clogTyCon
      Div  -> typeNatDivTyCon  ;  GeC -> geCTyCon  ;  FLog  -> flogTyCon
      Mod  -> typeNatModTyCon  ;  EqB -> eqBTyCon  ;  CLog2 -> clog2TyCon
      Log2 -> typeNatLogTyCon  ;  LtB -> ltBTyCon  ;  FLog2 -> flog2TyCon
      If   -> ifTyCon          ;  LeB -> leBTyCon  ;  Log   -> logTyCon
      And  -> andTyCon         ;  GtB -> gtBTyCon  ;  Min   -> minTyCon
      Or   -> orTyCon          ;  GeB -> geBTyCon  ;  Max   -> maxTyCon
      Not  -> notTyCon

  return KnownTypes{..}
 where
  lkup th = do
    nc <- hsc_NC . env_top <$> getEnv
    res <- liftIO $ thNameToGhcNameIO nc th
    maybe (fail $ "Failed to lookup " ++ show th) tcLookupTyCon res
