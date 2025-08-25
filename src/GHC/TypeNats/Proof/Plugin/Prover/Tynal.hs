{-# LANGUAGE DefaultSignatures #-}
module GHC.TypeNats.Proof.Plugin.Prover.Tynal
  ( Tynal
  , Term(..)
  , Signature(..)
  , LexicalFixity(..)
  , FixityDirection(..)
  , Fixity(..)
  , ProverFixities(..)
  , ProverEnv(..)
  , ProverConfig(..)
  , FromType(..)
  , specializeTerm
  , defPrintTerm
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
import GHC.Plugins (getOccString)
import GHC.Records (HasField(..))
import GHC.TypeNats (Nat)
import GHC.Types.Name (NamedThing(..))
import GHC.Types.Var (VarBndr(..), TyVar, tyVarKind)
import GHC.Utils.Outputable
  (Outputable(..), SDoc, (<+>), (<>), pprWithCommas, parens, colon, hsep, dot)
import System.FilePath ((</>))

import qualified Data.String.Combinators as S ((<+>), parens)

import GHC.TypeNats.Proof.Plugin.KnownTypes
  ( type (~>)(..), KnownTypes(..), fromTyCon
  )

-- | Tynal, an abbreviation for "type-nat language", is a small DSL
-- for describing terms over type level natural numbers. The DSL
-- functions as an interface between the more general Haskell 'Type'
-- and the corresponding representation within a proof assistant.
type Tynal = Term Constraint

-- | Base type classification.
class BaseType a where
  printBaseType ::
    (Monoid s, IsString s, ProverConfig p s) =>
    p -> a -> s

  showBaseType :: a -> String
  default showBaseType :: Show a => a -> String
  showBaseType = show

instance BaseType Bool where printBaseType = printBool
instance BaseType Nat  where printBaseType = printNat

-- | The context free grammar for describing Tynal terms.
data Term a where
  Lit :: BaseType a => a -> Term a
  Var :: TyVar -> Term a
  Op :: (a ~> b) -> Term (a ~> b)
  S :: Term (a ~> b) -> Term a -> Term b

instance Outputable (Term a) where
  ppr = \case
    Lit n -> fromString $ showBaseType n
    Var v -> ppr v
    Op op -> pprOp op
    S t0 t1 -> ppr t0 <+> parens (ppr t1)
   where
    pprOp :: (b ~> c) -> SDoc
    pprOp = \case
      NZero -> "(1 <=)"  ;  EqC  -> "(~)"   ;  LtC -> "(<)"    ;  LeC -> "(<=)"
      GtC   -> "(>)"     ;  GeC  -> "(>=)"  ;  EqB -> "(==)"   ;  LtB -> "(<?)"
      LeB   -> "(<=?)"   ;  GtB  -> "(>?)"  ;  GeB -> "(>=?)"  ;  And -> "(&&)"
      Or    -> "(||)"    ;  Not  -> "Not"   ;  If  -> "If"     ;  Add -> "(+)"
      Sub   -> "(-)"     ;  Mul  -> "(*)"   ;  Exp -> "(^)"    ;  Div -> "(/)"
      Mod   -> "Mod"     ;  Log2 -> "Log2"  ;  Min -> "Min"    ;  Max -> "Max"
      CLog2 -> "CLog2"   ;  FLog -> "FLog"  ;  GCD -> "GCD"    ;  LCM -> "LCM"
      FLog2 -> "FLog2"   ;  CLog -> "CLog"  ;  Log -> "Log"

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

data ProverEnv = ProverEnv
  { -- | the base directory specific to the prover
    proverDir :: FilePath
  , -- | the relative path for the module
    moduleDir :: FilePath
  }

-- | the full directory path specific to a prover and module
instance HasField "dir" ProverEnv FilePath where
  getField ProverEnv { .. } = proverDir </> moduleDir

-- | The class defines the interface for translation and verification
-- of Tynal terms with a proof assistant.
class ProverFixities p => ProverConfig p s where
  proverName :: p -> s

  -- | import requirements
  operatorImports :: p -> (a ~> b) -> s

  -- | print configuration
  printBool :: p -> Bool -> s
  default printBool :: IsString s => p -> Bool -> s
  printBool _ = fromString . show

  printNat :: p -> Nat -> s
  default printNat :: IsString s => p -> Nat -> s
  printNat _ = fromString . show

  printVar :: p -> TyVar -> s
  default printVar :: IsString s => p -> TyVar -> s
  printVar _ = fromString . getOccString

  printOp :: p -> (a ~> b) -> s

  printTerm :: p -> Term a -> s
  default printTerm :: (Monoid s, IsString s) => p -> Term a -> s
  printTerm = defPrintTerm

  printSignature :: p -> Signature Tynal -> s

  -- | the verification backend
  verify ::
    p ->
    -- | proof directories
    ProverEnv ->
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
  bOpFixity :: p -> (a ~> b ~> c) -> Fixity

-- | A 'Type' to Tynal term converter.
class FromType a where
  fromType :: KnownTypes -> Type -> Either Type a

instance FromType (Term Bool) where
  fromType kt@KnownTypes{..} = \case

    TyVarTy v -> return $ Var v
    TyConApp tc [] | tc == promotedTrueDataCon  -> return $ Lit True
    TyConApp tc [] | tc == promotedFalseDataCon -> return $ Lit False
    TyConApp tc [ty0]
      | Just (op :: Bool ~> Bool) <- fromTyCon kt tc
      -> do ty0' <- fromType kt ty0
            return $ Op op `S` ty0'

    TyConApp tc tys
      | tc == kOp EqB
      , [ty0, ty1] <- dropTKTypes tys
      -- We require equality to either monomorphize to the Nats or
      -- Bools. While technically being a limitation, we don't really
      -- loose any expressivity at this point, as the only meaningful
      -- proofs that don't require monomorphization turn out to be
      -- reflexivity, associativity, and transitivity, which GHC
      -- already can deduce on its own.
      , let natCase = do
              ty0' <- fromType kt ty0
              ty1' <- fromType kt ty1
              return $ Op (EqB :: Nat ~> Nat ~> Bool) `S` ty0' `S` ty1'
            boolCase = do
              ty0' <- fromType kt ty0
              ty1' <- fromType kt ty1
              return $ Op (EqB :: Bool ~> Bool ~> Bool) `S` ty0' `S` ty1'
      -> either (const boolCase) return natCase

    TyConApp tc tys
      | Just (op :: Nat ~> Nat ~> Bool) <- fromTyCon kt tc
      , [ty0, ty1] <- dropTKTypes tys
      -> do ty0' <- fromType kt ty0
            ty1' <- fromType kt ty1
            return $ Op op `S` ty0' `S` ty1'

    TyConApp tc tys
      | Just (op :: Bool ~> Bool ~> Bool) <- fromTyCon kt tc
      , [ty0, ty1] <- dropTKTypes tys
      -> do ty0' <- fromType kt ty0
            ty1' <- fromType kt ty1
            return $ Op op `S` ty0' `S` ty1'

    TyConApp tc tys
      | Just (op :: Bool ~> Bool ~> Bool ~> Bool) <- fromTyCon kt tc
      , [ty0, ty1, ty2] <- dropTKTypes tys
      -> do ty0' <- fromType kt ty0
            ty1' <- fromType kt ty1
            ty2' <- fromType kt ty2
            return $ Op op `S` ty0' `S` ty1' `S` ty2'
    ty -> Left ty

instance FromType (Term Nat) where
  fromType kt = \case
    TyVarTy v -> return $ Var v
    LitTy lit -> case lit of
      NumTyLit n -> return $ Lit $ fromInteger n
      _ -> Left $ LitTy lit
    TyConApp tc [ty0]
      | Just (op :: Nat ~> Nat) <- fromTyCon kt tc
      -> do ty0' <- fromType kt ty0
            return $ Op op `S` ty0'
    TyConApp tc [ty0, ty1]
      | Just (op :: Nat ~> Nat ~> Nat) <- fromTyCon kt tc
      -> do ty0' <- fromType kt ty0
            ty1' <- fromType kt ty1
            return $ Op op `S` ty0' `S` ty1'
    TyConApp tc tys
      | Just (op :: Bool ~> Nat ~> Nat ~> Nat) <- fromTyCon kt tc
      , [ty0, ty1, ty2] <- dropTKTypes tys
      -> do ty0' <- fromType kt ty0
            ty1' <- fromType kt ty1
            ty2' <- fromType kt ty2
            return $ Op op `S` ty0' `S` ty1' `S` ty2'
    ty -> Left ty

instance FromType (Term Constraint) where
  fromType kt@KnownTypes{..} = \case
    TyConApp tc tys
      | Just (op :: Nat ~> Constraint) <- fromTyCon kt tc
      , [ty0] <- dropTKTypes tys
      -> do ty0' <- fromType kt ty0
            return $ Op op `S` ty0'

    TyConApp tc tys
      | tc == kOp EqC
      , [ty0, ty1] <- dropTKTypes tys
      -- We require equality to either monomorphize to the Nats or
      -- Bools. While technically being a limitation, we don't really
      -- loose any expressivity at this point, as the only meaningful
      -- proofs that don't require monomorphization turn out to be
      -- reflexivity, associativity, and transitivity, which GHC
      -- already can deduce on its own.
      , let natCase = do
              ty0' <- fromType kt ty0
              ty1' <- fromType kt ty1
              return $ Op (EqC :: Nat ~> Nat ~> Constraint) `S` ty0' `S` ty1'
            boolCase = do
              ty0' <- fromType kt ty0
              ty1' <- fromType kt ty1
              return $ Op (EqC :: Bool ~> Bool ~> Constraint) `S` ty0' `S` ty1'
      -> either (const boolCase) return natCase

    TyConApp tc tys
      | Just (op :: Nat ~> Nat ~> Constraint) <- fromTyCon kt tc
      , [ty0, ty1] <- dropTKTypes tys
      -> do ty0' <- fromType kt ty0
            ty1' <- fromType kt ty1
            return $ Op op `S` ty0' `S` ty1'

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
            return $ Op (op :: Nat ~> Nat ~> Constraint) `S` ty0' `S` ty1'

    ty -> Left ty

-- | Rewrites some special cases.
specializeTerm :: Term a -> Term a
specializeTerm = \case
  Op LeC  `S` (Lit 1) `S` t -> Op NZero `S` specializeTerm t
  Op CLog `S` (Lit 2) `S` t -> Op CLog2 `S` specializeTerm t
  Op FLog `S` (Lit 2) `S` t -> Op FLog2 `S` specializeTerm t
  Op op `S` t -> Op op `S` specializeTerm t
  t0 `S` t1 -> specializeTerm t0 `S` specializeTerm t1
  x -> x

defPrintTerm ::
  forall p s a.
  (Monoid s, IsString s, ProverConfig p s) =>
  p -> Term a -> s
defPrintTerm p = \case
  -- ternary operators
  Op op `S` t0 `S` t1 `S` t2 -> pOp S.<+> pr t0 S.<+> pr t1 S.<+> pr t2
   where
    pOp = printOp p op

    pr :: Term u -> s
    pr t = par t $ printTerm p t

    par :: Term u -> s -> s
    par = \case { Lit{} -> id ; Var{} -> id ; _ -> S.parens }

  -- binary operators
  Op op `S` t0 `S` t1 -> case pPrefix of
    Prefix -> pOp S.<+> pr InfixL t0 S.<+> pr InfixR t1
    Infix  -> pr InfixL t0 S.<+> pOp S.<+> pr InfixR t1
   where
    Fixity level fixity pPrefix = bOpFixity p op
    pOp = printOp p op

    pr :: FixityDirection -> Term u -> s
    pr fx t = par fx t $ printTerm p t

    par :: FixityDirection -> Term u -> s -> s
    par fx = \case
      Op _ `S` _ `S` _ `S` _ -> S.parens
      Op op' `S` _ `S` _ -> case pPrefix' of
        Prefix                 -> S.parens
        Infix | level' < level -> S.parens
              | level' > level -> id
              | fx == fixity   -> id
              | otherwise      -> S.parens
       where
        Fixity level' _ pPrefix' = bOpFixity p op'
      _ -> id

  -- unary operators
  Op op `S` t0 -> printOp p op S.<+> par (printTerm p t0)
   where
    par = case t0 of
      Lit{} -> id
      Var{} -> id
      _     -> S.parens

  Op op -> printOp p op

  t0 `S` t1 -> printTerm p t0 S.<+> S.parens (printTerm p t1)
  Lit x -> printBaseType p x
  Var n -> printVar p n

-- | Extract the required imports from a Tynal term.
requiredImports ::
  forall p s. (Ord s, ProverConfig p s) =>
  p -> Signature Tynal -> [s]
requiredImports p Signature{..} =
  toAscList $ foldl imports (foldl imports empty sigPremise) sigConclusion
 where
  imports :: forall a. Set s -> Term a -> Set s
  imports a = \case
    Op op -> insert (operatorImports p op) a
    S t0 t1 -> imports (imports a t0) t1
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
