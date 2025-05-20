module GHC.TypeNats.Proof.Plugin.Prover.Coq
  ( Coq(..)
  ) where

import Prelude hiding (unwords)

import Data.String.Combinators
  ((<+>), colon, comma, punctuate, unwords)
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

-- | The type level witness of the Coq configuration.
data Coq = CoqConfig

instance (IsString s, Monoid s) => ProverConfig Coq s where
  proverName _ = "Coq"

  operatorImports _ = \case
    EqC -> "Coq.Init.Logic"  ;  Mod  -> "Coq.Init.Nat"
    LtC -> "Coq.Init.Peano"  ;  Min  -> "Coq.Init.Nat"
    LeC -> "Coq.Init.Peano"  ;  Max  -> "Coq.Init.Nat"
    GtC -> "Coq.Init.Peano"  ;  Log2 -> "Coq.Init.Nat"
    GeC -> "Coq.Init.Peano"  ;  FLog -> ""
    Add -> "Coq.Init.Nat"    ;  CLog -> ""
    Sub -> "Coq.Init.Nat"    ;  Log  -> ""
    Mul -> "Coq.Init.Nat"    ;  GCD  -> "Coq.Init.Nat"
    Exp -> "Coq.Init.Nat"    ;  LCM  -> ""
    Div -> "Coq.Init.Nat"

  printLit _ = fromString . show
  printVar _ = fromString . getOccString
  printOp _ = \case
    EqC -> "="      ;  LtC -> "<"    ;  LeC -> "<="   ;  GtC  -> ">"
    GeC -> ">="     ;  Add -> "+"    ;  Sub -> "-"    ;  Log  -> "NO PRIMITIVE"
    Mul -> "*"      ;  Exp -> "^"    ;  Div -> "/"    ;  CLog -> "NO PRIMITIVE"
    Mod -> "mod"    ;  Min -> "min"  ;  Max -> "max"  ;  FLog -> "NO PRIMITIVE"
    Log2 -> "log2"  ;  GCD -> "gcd"  ;  LCM -> "NO PRIMITIVE"

  printSignature p Signature{..} = unwords $
    [ name <> colon, "forall", unwords vars <> comma ]
    <> ((<+> "->") . printTerm p <$> sigPremise)
    <> punctuate " &&" (printTerm p <$> sigConclusion)
   where
    name = fromString $ getOccString $ getName sigClass
    vars = fromString . getOccString <$> sigVars

  verify p dir preamble sig@Signature{..} proof = do
    -- Write the proof to the file
    writeFile (dir </> fileName) $ unlines $
      [ ("Require Import" <+> imp) <> "."
      | imp <- requiredImports p sig
      ] <>
      [ ""
      ] <>
      (unpackFS <$> preamble) <>
      [ ""
      , "Lemma" <+> ("hs" <> printSignature p sig <> ".")
      , unpackFS proof
      , "Qed."
      ]
    -- Run the proof in Coq
    findExecutable "coqc" >>= \case
      Just coqc -> withCurrentDirectory dir $ do
        (exitCode, _, output) <- readProcessWithExitCode coqc [fileName] ""
        if exitCode == ExitSuccess then
          return Nothing
        else
          return $ Just $ fromString output
      Nothing -> return $ Just "Failure: coqc not present on the system."

   where
    fileName = getOccString (getName sigClass) <.> "v"

instance ProverFixities Coq where
  bOpFixity _ = \case
    EqC -> Fixity 4 InfixN Infix   ;  LtC  -> Fixity 4 InfixN Infix
    LeC -> Fixity 4 InfixN Infix   ;  GtC  -> Fixity 4 InfixN Infix
    GeC -> Fixity 4 InfixN Infix   ;  Add  -> Fixity 6 InfixL Infix
    Sub -> Fixity 6 InfixL Infix   ;  Mul  -> Fixity 7 InfixL Infix
    Exp -> Fixity 8 InfixL Infix   ;  Div  -> Fixity 7 InfixL Infix
    Mod -> Fixity 7 InfixL Infix   ;  Min  -> Fixity 9 InfixL Prefix
    Max -> Fixity 9 InfixL Prefix  ;  FLog -> Fixity 9 InfixL Prefix
    Log -> Fixity 9 InfixL Prefix  ;  CLog -> Fixity 9 InfixL Prefix
    GCD -> Fixity 9 InfixL Prefix  ;  LCM  -> Fixity 9 InfixL Prefix
