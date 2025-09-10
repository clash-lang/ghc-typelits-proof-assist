module GHC.TypeNats.Proof.Plugin.Prover.Coq
  ( Coq(..)
  ) where

import Prelude hiding (unwords)

import Data.String.Combinators
  ((<+>), colon, comma, parens, punctuate, unwords)
import Data.String (IsString(..))
import GHC.Builtin.Types (boolTy, naturalTy)
import GHC.Data.FastString (unpackFS)
import GHC.Plugins (getOccString)
import GHC.Tc.Utils.TcType (eqType)
import GHC.Types.Name (NamedThing(..))
import GHC.Types.Var (tyVarKind)
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
    NZero -> "Coq.Init.Logic"  ;  Add   -> "Coq.Init.Nat"
    EqC   -> "Coq.Init.Logic"  ;  Sub   -> "Coq.Init.Nat"
    LtC   -> "Coq.Init.Logic"  ;  Mul   -> "Coq.Init.Nat"
    LeC   -> "Coq.Init.Logic"  ;  Exp   -> "Coq.Init.Nat"
    GtC   -> "Coq.Init.Logic"  ;  Div   -> "Coq.Init.Nat"
    GeC   -> "Coq.Init.Logic"  ;  Mod   -> "Coq.Init.Nat"
    EqB   -> ""                ;  Min   -> "Coq.Init.Nat"
    LtB   -> "Coq.Init.Nat"    ;  Max   -> "Coq.Init.Nat"
    LeB   -> "Coq.Init.Nat"    ;  Log2  -> "Coq.Init.Nat"
    GtB   -> "Coq.Init.Nat"    ;  CLog2 -> "Coq.Init.Nat"
    GeB   -> "Coq.Init.Nat"    ;  GCD   -> "Coq.Init.Nat"
    And   -> "Bool"            ;  LCM   -> "Coq.Init.Nat"
    Or    -> "Bool"            ;  FLog2 -> ""
    Not   -> "Bool"            ;  Log   -> ""
    If    -> ""                ;  CLog  -> ""
    FLog  -> ""

  printOp _ = \case
    EqB   -> "=?"   ;  LtB -> "<?"    ;  LeB   -> "<=?"
    GtB   -> ""     ;  GeB -> ""      ;  NZero -> "1 <="
    EqC   -> "="    ;  LtC -> "<"     ;  LeC   -> "<="
    GtC   -> ">"    ;  GeC -> ">="    ;  And   -> "&&"
    Or    -> "||"   ;  Not -> "negb"  ;  If    -> "if"
    Add   -> "+"    ;  Sub -> "-"     ;  Log2  -> "log2"
    Mul   -> "*"    ;  Exp -> "^"     ;  FLog2 -> "log2"
    Div   -> "/"    ;  Mod -> "mod"   ;  Min   -> "min"
    Max   -> "max"  ;  GCD -> "gcd"   ;  LCM   -> "Nat.lcm"
    CLog  -> "NO PRIMITIVE"  ;  FLog -> "NO PRIMITIVE"
    CLog2 -> "NO PRIMITIVE"  ;  Log  -> "NO PRIMITIVE"

  printBool _ = \case
    True  -> "true"
    False -> "false"

  printTerm p = \case
    Op GtB `S` t0 `S` t1 -> printTerm p $ Op LtB `S` t1 `S` t0
    Op GeB `S` t0 `S` t1 -> printTerm p $ Op LeB `S` t1 `S` t0
    Op EqC `S` t0 `S` t1 ->
      (parens (printTerm p t0) <> "%nat")
         <+> printOp p EqC
         <+> (parens (printTerm p t1) <> "%nat")
    Op NZero `S` t -> "1 <=" <+> (parens (printTerm p t) <> "%nat")
    Op If `S` t0 `S` t1 `S` t2 ->
      "if" <+> printTerm p t0 <+>
      "then" <+> printTerm p t1 <+>
      "else" <+> printTerm p t2
    t -> defPrintTerm p t

  printSignature p Signature{..} = unwords $
    [ name <> colon, "forall", unwords vars <> comma ]
    <> ((<+> "->") . printTerm p <$> sigPremise)
    <> punctuate " &&" (printTerm p <$> sigConclusion)
   where
    name = fromString $ getOccString $ getName sigClass
    vars = prSigVar <$> sigVars
    prSigVar x
      | tyk `eqType` boolTy    = parens $ var <+> colon <+> "bool"
      | tyk `eqType` naturalTy = parens $ var <+> colon <+> "nat"
      | otherwise              = var
     where
      tyk = tyVarKind x
      var = fromString $ getOccString x

  verify p dir preamble sig@Signature{..} proof = do
    -- Write the proof to the file
    writeFile (dir </> fileName) $ unlines $
      [ ("Require Import" <+> imp) <> "."
      | imp <- "Coq.Init.Peano" : requiredImports p sig
      , not $ null imp
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
    EqB -> Fixity 4 InfixN Infix   ;  LtB  -> Fixity 4 InfixN Infix
    LeB -> Fixity 4 InfixN Infix   ;  GtB  -> Fixity 4 InfixN Infix
    GeB -> Fixity 4 InfixN Infix   ;  EqC  -> Fixity 4 InfixN Infix
    LtC -> Fixity 4 InfixN Infix   ;  LeC  -> Fixity 4 InfixN Infix
    GtC -> Fixity 4 InfixN Infix   ;  GeC  -> Fixity 4 InfixN Infix
    And -> Fixity 6 InfixR Infix   ;  Or   -> Fixity 5 InfixR Infix
    If  -> Fixity 0 InfixN Prefix  ;  Add  -> Fixity 6 InfixL Infix
    Sub -> Fixity 6 InfixL Infix   ;  Mul  -> Fixity 7 InfixL Infix
    Exp -> Fixity 8 InfixL Infix   ;  Div  -> Fixity 7 InfixL Infix
    Mod -> Fixity 7 InfixL Infix   ;  Min  -> Fixity 9 InfixL Prefix
    Max -> Fixity 9 InfixL Prefix  ;  FLog -> Fixity 9 InfixL Prefix
    Log -> Fixity 9 InfixL Prefix  ;  CLog -> Fixity 9 InfixL Prefix
    GCD -> Fixity 9 InfixL Prefix  ;  LCM  -> Fixity 9 InfixL Prefix
