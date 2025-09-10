module GHC.TypeNats.Proof.Plugin.Prover.Agda
  ( Agda(..)
  ) where

import Prelude hiding (unwords)

import Data.Either (partitionEithers)
import Data.String.Combinators
  ((<+>), parens, colon, punctuate, unwords)
import Data.String (IsString(..))
import GHC.Data.FastString (unpackFS)
import GHC.Plugins (getOccString)
import GHC.Types.Name (NamedThing(..))
import GHC.Types.Var (TyVar)
import System.Directory (findExecutable, withCurrentDirectory)
import System.Exit (ExitCode(..))
import System.FilePath ((</>), (<.>))
import System.Process (readProcessWithExitCode)

import GHC.TypeNats.Proof.Plugin.KnownTypes
import GHC.TypeNats.Proof.Plugin.Prover.Tynal

-- | The type level witness of the Agda configuration.
data Agda = AgdaConfig

instance (IsString s, Monoid s) => ProverConfig Agda s where
  proverName _ = "Agda"

  operatorImports _ = \case
    EqC   -> "Agda.Builtin.Equality"  ;  And   -> "Data.Bool.Base hiding (_≤_;_<_)"
    EqB   -> "Agda.Builtin.Equality"  ;  Not   -> "Data.Bool.Base hiding (_≤_;_<_)"
    NZero -> "Data.Nat.Base"          ;  Or    -> "Data.Bool.Base hiding (_≤_;_<_)"
    LtC   -> "Data.Nat.Base"          ;  If    -> "Data.Bool.Base hiding (_≤_;_<_)"
    LeC   -> "Data.Nat.Base"          ;  Log2  -> "Data.Nat.Logarithm"
    GtC   -> "Data.Nat.Base"          ;  CLog2 -> "Data.Nat.Logarithm"
    GeC   -> "Data.Nat.Base"          ;  FLog2 -> "Data.Nat.Logarithm"
    LtB   -> "Data.Nat.Base"          ;  Add   -> "Agda.Builtin.Nat"
    LeB   -> "Data.Nat.Base"          ;  Sub   -> "Agda.Builtin.Nat"
    GtB   -> "Data.Nat.Base"          ;  Mul   -> "Agda.Builtin.Nat"
    GeB   -> "Data.Nat.Base"          ;  GCD   -> "Data.Nat.GCD"
    Min   -> "Data.Nat.Base"          ;  LCM   -> "Data.Nat.LCM"
    Max   -> "Data.Nat.Base"          ;  Log   -> ""
    Exp   -> "Data.Nat.Base"          ;  CLog  -> ""
    Div   -> "Data.Nat.Base"          ;  FLog  -> ""
    Mod   -> "Data.Nat.Base"

  printOp _ = \case
    EqB -> "≡ᵇ"  ;  LtB -> "<ᵇ"  ;  LeB -> "≤ᵇ"   ;  GtB    -> ""
    GeB -> ""    ;  EqC -> "≡"   ;  LtC -> "<"    ;  NZero  -> "NonZero"
    LeC -> "≤"   ;  GtC -> ">"   ;  GeC -> "≥"    ;  Log2   -> "⌊log₂_⌋"
    Add -> "+"   ;  Sub -> "-"   ;  Mul -> "*"    ;  CLog2  -> "⌈log₂_⌉"
    Exp -> "^"   ;  Div -> "/"   ;  Mod -> "%"    ;  FLog2  -> "⌊log₂_⌋"
    Min -> "⊓"   ;  Max -> "⊔"   ;  GCD -> "gcd"  ;  LCM    -> "lcm"
    And -> "∧"   ;  Or  -> "∨"   ;  Not -> "not"  ;  If     -> "if_then_else_"
    Log -> "NO PRIMITIVE"  ;  CLog  -> "NO PRIMITIVE"  ;  FLog -> "NO PRIMITIVE"

  printBool _ = \case
    True  -> "true"
    False -> "false"

  printTerm p = \case
    Op GtB `S` t0 `S` t1 -> printTerm p $ Op LtB `S` t1 `S` t0
    Op GeB `S` t0 `S` t1 -> printTerm p $ Op LeB `S` t1 `S` t0
    t -> defPrintTerm p t

  printSignature p Signature{..} = unwords $
    [ name, colon , parens (unwords $ vars <> [ colon, "ℕ" ]) ]
    <> ((".{{_ : NonZero " <>) . (<> "}}") . fromString . getOccString <$> nzs)
    <> [ "→" ] <> ((<+> "→") . printTerm p <$> premise)
    <> punctuate " ∧" (printTerm p <$> sigConclusion)
   where
    (nzs, premise) = partitionEithers $ partNZVar <$> sigPremise
    name = fromString $ getOccString $ getName sigClass
    vars = fromString . getOccString <$> sigVars

    partNZVar :: Term a -> Either TyVar (Term a)
    partNZVar = \case
      Op NZero `S` Var v -> Left v
      x -> Right x

  verify p env preamble sig@Signature{..} proof = do
    -- Write the proof to the file
    writeFile (env.dir </> fileName) $ unlines $
      [ "open import" <+> imp
      | imp <- requiredImports p sig
      , not $ null imp
      ] <>
      [ ""
      ] <>
      (unpackFS <$> preamble) <>
      [ ""
      , printSignature p sig
      , unpackFS proof
      ]

    -- Run the proof in Coq
    findExecutable "agda" >>= \case
      Just agda -> withCurrentDirectory env.dir $ do
        (exitCode, output, _) <- readProcessWithExitCode agda [fileName] ""
        if exitCode == ExitSuccess then
          return Nothing
        else
          return $ Just $ fromString output
      Nothing -> return $ Just "Failure: agda not present on the system."
   where
    fileName = getOccString (getName sigClass) <.> "agda"

instance ProverFixities Agda where
  bOpFixity _ = \case
    EqB -> Fixity 4 InfixN Infix   ;  LtB  -> Fixity 4 InfixN Infix
    LeB -> Fixity 4 InfixN Infix   ;  GtB  -> Fixity 4 InfixN Infix
    GeB -> Fixity 4 InfixN Infix   ;  EqC  -> Fixity 4 InfixN Infix
    LtC -> Fixity 4 InfixN Infix   ;  LeC  -> Fixity 4 InfixN Infix
    GtC -> Fixity 4 InfixN Infix   ;  GeC  -> Fixity 4 InfixN Infix
    And -> Fixity 6 InfixR Infix   ;  Or   -> Fixity 5 InfixR Infix
    If  -> Fixity 0 InfixN Prefix  ;  Add  -> Fixity 6 InfixL Infix
    Sub -> Fixity 6 InfixL Infix   ;  Mul  -> Fixity 7 InfixL Infix
    Exp -> Fixity 8 InfixR Infix   ;  Div  -> Fixity 7 InfixL Infix
    Mod -> Fixity 7 InfixL Infix   ;  Min  -> Fixity 7 InfixL Infix
    Max -> Fixity 6 InfixL Infix   ;  FLog -> Fixity 9 InfixL Prefix
    Log -> Fixity 9 InfixL Prefix  ;  CLog -> Fixity 9 InfixL Prefix
    GCD -> Fixity 9 InfixL Prefix  ;  LCM  -> Fixity 9 InfixL Prefix
