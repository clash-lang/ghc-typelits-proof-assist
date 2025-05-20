module GHC.TypeNats.Proof.Plugin.Prover.Agda
  ( Agda(..)
  ) where

import Prelude hiding (unwords)

import Data.String.Combinators
  ((<+>), parens, colon, punctuate, unwords)
import Data.String (IsString(..))
import GHC.Data.FastString (unpackFS)
import GHC.Plugins (getOccString)
import GHC.Types.Name (NamedThing(..))
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
    EqC -> "Agda.Builtin.Equality"  ;  Mod  -> "Data.Nat.Base"
    LtC -> "Data.Nat.Base"          ;  Min  -> "Data.Nat.Base"
    LeC -> "Data.Nat.Base"          ;  Max  -> "Data.Nat.Base"
    GtC -> "Data.Nat.Base"          ;  Log2 -> ""
    GeC -> "Data.Nat.Base"          ;  FLog -> ""
    Add -> "Agda.Builtin.Nat"       ;  CLog -> ""
    Sub -> "Agda.Builtin.Nat"       ;  Log  -> ""
    Mul -> "Agda.Builtin.Nat"       ;  GCD  -> "Data.Nat.GCD"
    Exp -> "Data.Nat.Base"          ;  LCM  -> "Data.Nat.LCM"
    Div -> "Data.Nat.Base"

  printLit _ = fromString . show
  printVar _ = fromString . getOccString
  printOp _ = \case
    EqC -> "≡"    ;  LtC -> "<"    ;  LeC -> "≤"  ;  GtC  -> ">"
    GeC -> "≥"    ;  Add -> "+"    ;  Sub -> "-"  ;  Log2 -> "NO PRIMITIVE"
    Mul -> "*"    ;  Exp -> "^"    ;  Div -> "/"  ;  CLog -> "NO PRIMITIVE"
    Mod -> "%"    ;  Min -> "⊓"    ;  Max -> "⊔"  ;  FLog -> "NO PRIMITIVE"
    GCD -> "gcd"  ;  LCM -> "lcm"  ;  Log -> "NO PRIMITIVE"

  printSignature p Signature{..} = unwords $
    [ name, colon , parens (unwords $ vars <> [ colon, "ℕ" ]), "→" ]
    <> ((<+> "→") . printTerm p <$> sigPremise)
    <> punctuate " ∧" (printTerm p <$> sigConclusion)
   where
    name = fromString $ getOccString $ getName sigClass
    vars = fromString . getOccString <$> sigVars

  verify p dir preamble sig@Signature{..} proof = do
    -- Write the proof to the file
    writeFile (dir </> fileName) $ unlines $
      [ "open import" <+> imp
      | imp <- requiredImports p sig
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
      Just agda -> withCurrentDirectory dir $ do
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
    EqC -> Fixity 4 InfixN Infix   ;  LtC  -> Fixity 4 InfixN Infix
    LeC -> Fixity 4 InfixN Infix   ;  GtC  -> Fixity 4 InfixN Infix
    GeC -> Fixity 4 InfixN Infix   ;  Add  -> Fixity 6 InfixL Infix
    Sub -> Fixity 6 InfixL Infix   ;  Mul  -> Fixity 7 InfixL Infix
    Exp -> Fixity 8 InfixR Infix   ;  Div  -> Fixity 7 InfixL Infix
    Mod -> Fixity 7 InfixL Infix   ;  Min  -> Fixity 7 InfixL Infix
    Max -> Fixity 6 InfixL Infix   ;  FLog -> Fixity 9 InfixL Prefix
    Log -> Fixity 9 InfixL Prefix  ;  CLog -> Fixity 9 InfixL Prefix
    GCD -> Fixity 9 InfixL Prefix  ;  LCM  -> Fixity 9 InfixL Prefix
