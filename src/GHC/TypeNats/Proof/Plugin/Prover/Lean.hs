module GHC.TypeNats.Proof.Plugin.Prover.Lean where

import Prelude hiding (unwords)

import Data.String (IsString (fromString))
import Data.String.Combinators (unwords, (<+>), punctuate, parens)
import GHC.Data.FastString (unpackFS)
import GHC.Plugins (getOccString)
import GHC.Types.Name (NamedThing(..))
import System.Directory (withCurrentDirectory, findExecutable)
import System.Exit (ExitCode(..))
import System.FilePath ((</>), (<.>))
import System.Process (readProcessWithExitCode)

import GHC.TypeNats.Proof.Plugin.KnownTypes
import GHC.TypeNats.Proof.Plugin.Prover.Tynal

data Lean = LeanConfig

instance (IsString s, Monoid s) => ProverConfig Lean s where
  proverName _ = "Lean"

  operatorImports _ = \case
    NZero -> ""  ;  Add   -> ""
    EqC   -> ""  ;  Sub   -> ""
    LtC   -> ""  ;  Mul   -> ""
    LeC   -> ""  ;  Exp   -> ""
    GtC   -> ""  ;  Div   -> ""
    GeC   -> ""  ;  Mod   -> ""
    EqB   -> ""  ;  Min   -> ""
    LtB   -> ""  ;  Max   -> ""
    LeB   -> ""  ;  Log2  -> ""
    GtB   -> ""  ;  CLog2 -> "Mathlib.Data.Nat.Log"
    GeB   -> ""  ;  GCD   -> ""
    And   -> ""  ;  LCM   -> ""
    Or    -> ""  ;  FLog2 -> ""
    Not   -> ""  ;  Log   -> "Mathlib.Data.Nat.Log"
    If    -> ""  ;  CLog  -> "Mathlib.Data.Nat.Log"
    FLog  -> "Mathlib.Data.Nat.Log"

  printBool _ = \case
    True  -> "true"
    False -> "false"

  printOp _ = \case
    LtC   -> "<"  ;  LeC -> "≤"  ;  EqC -> "="  ;  GeC -> "≥"  ;  GtC -> ">"
    Add   -> "+"  ;  Mul -> "*"  ;  Exp -> "^"        ;  CLog -> "Nat.clog"
    Sub   -> "-"  ;  Div -> "/"  ;  Log -> "Nat.log"  ;  FLog -> "Nat.log"
    LtB   -> "Nat.blt"   ;  LeB   -> "Nat.ble"   ;  EqB   -> "=="
    GeB   -> "Nat.bge"   ;  GtB   -> "Nat.bgt"   ;  If    -> "Bool.cond"
    Not   -> "Bool.not"  ;  And   -> "&&"        ;  Or    -> "||"
    Log2  -> "Nat.log2"  ;  FLog2 -> "Nat.log2"  ;  CLog2 -> "Nat.clog 2"
    Mod   -> "%"         ;  GCD   -> "Nat.gcd"   ;  LCM   -> "Nat.lcm"
    NZero -> "0 ≠"       ;  Min   -> "min"       ;  Max   -> "max"

  printTerm p = \case
    Op If `S` t0 `S` t1 `S` t2 ->
      "bif" <+> printTerm p t0 <+>
      "then" <+> printTerm p t1 <+>
      "else" <+> printTerm p t2
    t -> defPrintTerm p t

  printSignature p Signature{..} = unwords $
    [ name <+> unwords [parens (v <+> ": Nat") | v <- vars], ":" ] <> assertion
   where
    name       = fromString $ getOccString $ getName sigClass
    vars       = fromString . getOccString <$> sigVars
    conclusion = unwords $ punctuate " ∧" $ printTerm p <$> sigConclusion
    assertion  = punctuate " →" $ (printTerm p <$> sigPremise) <> [conclusion]

  verify p env preamble sig@Signature{..} proof = do
    let fileName = getOccString (getName sigClass) <.> "lean"

    writeFile (env.dir </> fileName) $ unlines $
      [ "import" <+> imp
      | imp <- requiredImports p sig
      , not (null imp)
      ] <>
      [ ""
      ] <>
      (unpackFS <$> preamble) <>
      [ ""
      , "theorem" <+> ("hs" <> printSignature p sig) <+> ":=" <+> "by"
      , unpackFS proof
      ]

    findExecutable "lake" >>= \case
      Just lake -> withCurrentDirectory env.proverDir $ do
        let relativePath = env.moduleDir </> fileName
        (exitCode, outputStd, outputErr) <-
          readProcessWithExitCode lake ["env", "lean", relativePath] ""
        if exitCode == ExitSuccess then
          return Nothing
        else
          return $ Just $ fromString (outputStd <> outputErr)
      Nothing ->
        return $ Just "Failure: lean not present on the system."

instance ProverFixities Lean where
  -- Taken from:
  -- * https://github.com/leanprover/lean4/blob/a4f38cc78250f4c7f813c8d20700d97a53f0d3d6/src/Init/Notation.lean
  -- * https://github.com/leanprover/lean4/blob/a4f38cc78250f4c7f813c8d20700d97a53f0d3d6/src/Init/Core.lean

  -- Note that Lean supports defining custom mixfix notation, where the required
  -- fixity of arguments and the returned fixity of the full expression are
  -- specified separately. An example of this is @!@ (the preferred spelling of
  -- @Bool.not@), where the argument has fixity 40, and the result has fixity
  -- 1024. This means an expression like @Bool.not !0 == 1@ means
  -- @Bool.not (!(0 == 1))@. Upgrading the pretty-printer to support this would
  -- be hard: a naive implementation might e.g. misprint:
  --   @Bool.and (!0 == 1) (!0 == 1)@
  -- as:
  --   @Bool.and !0 == 1 !0 == 1@
  -- whereas the minimum parentheses required are:
  --   @Bool.and (!0 == 1) !0 == 1@.
  -- For details, see
  -- https://github.com/leanprover/lean4/blob/a4f38cc78250f4c7f813c8d20700d97a53f0d3d6/src/Lean/PrettyPrinter/Parenthesizer.lean
  -- For now we only support operators that are infix[l/r/n] or prefix, and
  -- otherwise we use the explicit function name. The exception is @If@, which,
  -- being a ternary operator, is always parenthesized anyway.

  bOpFixity _ = \case
    EqB  -> Fixity 50   InfixN Infix   ;  LtB  -> Fixity 90   InfixL Prefix
    LeB  -> Fixity 90   InfixL Prefix  ;  GtB  -> Fixity 90   InfixL Prefix
    GeB  -> Fixity 90   InfixL Prefix  ;  EqC  -> Fixity 50   InfixN Infix
    LtC  -> Fixity 50   InfixN Infix   ;  LeC  -> Fixity 50   InfixN Infix
    GtC  -> Fixity 50   InfixN Infix   ;  GeC  -> Fixity 50   InfixN Infix
    And  -> Fixity 35   InfixL Infix   ;  Or   -> Fixity 30   InfixL Infix
    If   -> Fixity 1022 InfixL Prefix  ;  Add  -> Fixity 65   InfixL Infix
    Sub  -> Fixity 65   InfixL Infix   ;  Mul  -> Fixity 70   InfixL Infix
    Exp  -> Fixity 80   InfixR Infix   ;  Div  -> Fixity 70   InfixL Infix
    Mod  -> Fixity 70   InfixL Infix   ;  Min  -> Fixity 90   InfixL Prefix
    Max  -> Fixity 90   InfixL Prefix  ;  FLog -> Fixity 90   InfixL Prefix
    Log  -> Fixity 90   InfixL Prefix  ;  CLog -> Fixity 90   InfixL Prefix
    GCD  -> Fixity 90   InfixL Prefix  ;  LCM  -> Fixity 90   InfixL Prefix
