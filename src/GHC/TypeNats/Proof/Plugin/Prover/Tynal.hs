module GHC.TypeNats.Proof.Plugin.Prover.Tynal
  ( Tynal
  , Term(..)
  , Signature(..)
  , LexicalFixity(..)
  , FixityDirection(..)
  , Fixity(..)
  , ProverFixities(..)
  , ProverConfig(..)
  , FromType(..)
  , printTerm
  , requiredImports
  , dropTKTypes
  , dropTKVars
  , toType
  ) where

import Prelude hiding ((<>))

import Data.List (find)
import Data.Set (Set, empty, toAscList, insert)
import Data.String (IsString(..))
import GHC.Base (Constraint)
import GHC.Builtin.Types
  (promotedFalseDataCon, promotedTrueDataCon, cTupleTyCon, multMulTyCon)
import GHC.Builtin.Types.Literals (typeNatCmpTyCon)
import GHC.Core.Class (Class)
import GHC.Core.InstEnv (ClsInst)
import GHC.Core.TyCo.Rep (Type(..), TyLit(..), FunTyFlag(..), ForAllTyFlag(..))
import GHC.Core.Type (isTypeLikeKind, typeKind, mkTyConApp)
import GHC.Data.FastString (FastString)
import GHC.TypeNats (Nat)
import GHC.Types.Name (NamedThing(..))
import GHC.Types.Var (VarBndr(..), TyVar, tyVarKind)
import GHC.Utils.Outputable
  (Outputable(..), SDoc, (<+>), (<>), pprWithCommas, parens, colon,  hsep, dot)

import qualified Data.String.Combinators as S ((<+>), parens)

import GHC.TypeNats.Proof.Plugin.KnownTypes
  ( KnownTypes(..), KOp(..), fromTyCon
  )

-- | Tynal, an abbreviation for "type-nat language", is a small DSL
-- for describing terms over type level natural numbers. The DSL
-- functions as an interface between the more general Haskell 'Type'
-- and the corresponding representation within a proof assistant.
type Tynal = Term Constraint

-- | The context free grammar for describing Tynal terms.
data Term a where
  Lit :: Nat -> Term a
  Var :: TyVar -> Term a
  UOp :: KOp (a -> b) -> Term a -> Term b
  BOp :: KOp (a -> b -> c) -> Term a -> Term b -> Term c

instance Outputable (Term a) where
  ppr = \case
    Lit n -> fromString $ show n
    Var v -> ppr v
    UOp op t0 -> pOp op
      <+> parens (ppr t0)
    BOp op t0 t1 -> pOp op
      <+> parens (ppr t0)
      <+> parens (ppr t1)
   where
    pOp :: forall sig. KOp sig -> SDoc
    pOp = \case
      EqC  -> "(~)"   ;  LtC -> "(<)"  ;  LeC -> "(<=)" ;  GtC  -> "(>)"
      GeC  -> "(>=)"  ;  Add -> "(+)"  ;  Sub -> "(-)"  ;  Log  -> "Log"
      Mul  -> "(*)"   ;  Exp -> "(^)"  ;  Div -> "(/)"  ;  CLog -> "CLog"
      Mod  -> "Mod"   ;  Min -> "Min"  ;  Max -> "Max"  ;  FLog -> "FLog"
      Log2 -> "Log2"  ;  GCD -> "GCD"  ;  LCM -> "LCM"

-- | A generalized interface for signatures of a type level proof.
data Signature a = Signature
  { -- | the universally quantified variables appearing in the signature
    sigVars :: [TyVar]
  , -- | the premise of the proof
    sigPremise :: [a]
  , -- | the conclusion of the proof
    sigConclusion :: [a]
    -- | the corresponding Haskell instance describing the premises
  , sigInstance :: ClsInst
  , -- | the corresponding Haskell class describing the conclusions
    sigClass :: Class
  }

instance Outputable a => Outputable (Signature a) where
  ppr Signature{..} = ppr (getName sigClass) <+> colon <> colon
    <+> "forall" <+> hsep (ppr <$> sigVars) <> dot
    <+> parens (pprWithCommas ppr sigPremise) <+> "=>"
    <+> parens (pprWithCommas ppr sigConclusion)

-- | Lexical Operator Fixity.
data LexicalFixity
  = Prefix
  | Infix
  deriving (Eq)

-- | Operator Fixity Direction.
data FixityDirection
  = InfixL
  | InfixR
  | InfixN
  deriving (Eq)

-- | Operator Fixity.
data Fixity
  = Fixity Int FixityDirection LexicalFixity
  deriving (Eq)

-- | The class defines the interface for translation and verification
-- of Tynal terms with a proof assistant.
class ProverFixities p => ProverConfig p s where
  proverName :: p -> s

  -- | import requirements
  operatorImports :: p -> KOp sig -> s

  -- | print configuration
  printLit       :: p -> Nat -> s
  printVar       :: p -> TyVar -> s
  printOp        :: p -> KOp sig -> s
  printSignature :: p -> Signature Tynal -> s

  -- | the verification backend
  verify ::
    p ->
    -- | proof directory (must exist)
    FilePath ->
    -- | proof preamble
    [FastString] ->
    -- | proof signature
    Signature Tynal->
    -- | the actual proof
    FastString ->
    -- | Just an error message, in case of an error,
    -- or Nothing otherwise
    IO (Maybe s)

-- | A "sub-class" of 'ProverConfig' that does not require an
-- additional result type parameter
class ProverFixities p where
  bOpFixity :: p -> KOp (a -> b -> c) -> Fixity

-- | A 'Type' to Tynal term converter.
class FromType a where
  fromType :: KnownTypes -> Type -> Either Type a

instance FromType (Term Nat) where
  fromType kt = \case
    TyVarTy v -> return $ Var v
    LitTy lit -> case lit of
      NumTyLit n -> return $ Lit $ fromInteger n
      _ -> Left $ LitTy lit
    TyConApp tc [ty0]
      | Just op <- fromTyCon kt tc
      -> do ty0' <- fromType kt ty0
            return $ UOp (op :: KOp (Nat -> Nat)) ty0'
    TyConApp tc [ty0, ty1]
      | Just op <- fromTyCon kt tc
      -> do ty0' <- fromType kt ty0
            ty1' <- fromType kt ty1
            return $ BOp (op :: KOp (Nat -> Nat -> Nat)) ty0' ty1'
    ty -> Left ty

instance FromType (Term Constraint) where
  fromType kt@KnownTypes{..} = \case
    TyConApp tc tys
      | Just op <- fromTyCon kt tc
      , [ty0, ty1] <- dropTKTypes tys
      -> do ty0' <- fromType kt ty0
            ty1' <- fromType kt ty1
            return $ BOp (op :: KOp (Nat -> Nat -> Constraint)) ty0' ty1'
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
      -> do ty0' <- fromType kt ty0
            ty1' <- fromType kt ty1
            return $ BOp (op :: KOp (Nat -> Nat -> Constraint)) ty0' ty1'
    ty -> Left ty

-- | Tynal term printer.
printTerm ::
  forall p e s.
  (Monoid s, IsString s, ProverConfig p s) =>
  p -> Term e -> s
printTerm p = \case
  Lit x -> printLit p x
  Var n -> printVar p n
  UOp op t -> printOp p op S.<+> par (printTerm p t)
   where
    par = case t of
      Lit{} -> id
      Var{} -> id
      _     -> S.parens
  BOp op t0 t1 -> case pPrefix of
    Prefix -> pOp S.<+> fT0 S.<+> fT1
    Infix  -> fT0 S.<+> pOp S.<+> fT1
   where
    Fixity level fixity pPrefix = bOpFixity p op

    pOp = printOp p op
    fT0 = par InfixL t0 pT0
    fT1 = par InfixR t1 pT1

    pT0 = printTerm p t0
    pT1 = printTerm p t1

    par :: forall e'. FixityDirection -> Term e' -> s -> s
    par fx = \case
      Lit{} -> id  ;  Var{} -> id  ;  UOp{} -> id
      BOp op' _ _ -> case pPrefix' of
        Prefix                 -> S.parens
        Infix | level' < level -> S.parens
              | level' > level -> id
              | fx == fixity   -> id
              | otherwise      -> S.parens
       where
        Fixity level' _ pPrefix' = bOpFixity p op'

-- | Extract the required imports from a Tynal term.
requiredImports ::
  forall p s. (Ord s, ProverConfig p s) =>
  p -> Signature Tynal -> [s]
requiredImports p Signature{..} =
  toAscList $ foldl imports (foldl imports empty sigPremise) sigConclusion
 where
  imports :: forall a. Set s -> Term a -> Set s
  imports a = \case
    UOp op t0 -> imports (insert (operatorImports p op) a) t0
    BOp op t0 t1 ->
      imports (imports (insert (operatorImports p op) a) t0) t1
    _ -> a

-- | Drops the types that are of a TYPE like kind.
dropTKTypes :: [Type] -> [Type]
dropTKTypes = filter (not . isTypeLikeKind . typeKind)

-- | Drops the variables that are of a TYPE like kind.
dropTKVars :: [TyVar] -> [TyVar]
dropTKVars = filter (not . isTypeLikeKind . tyVarKind)

-- | For debugging purposes only.
toType :: Signature Type -> Type
toType Signature{..} = ty2
 where
  ty0 = mkTyConApp (cTupleTyCon $ length sigConclusion) sigConclusion
  ty1 = foldr (FunTy FTF_C_C (TyConApp multMulTyCon [])) ty0 sigPremise
  ty2 = foldr (\v -> ForAllTy (Bndr v Inferred)) ty1 sigVars
