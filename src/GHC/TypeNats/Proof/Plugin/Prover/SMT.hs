module GHC.TypeNats.Proof.Plugin.Prover.SMT
  ( SMT(..)
  ) where

import Prelude hiding (unwords, unlines)

import Data.String.Combinators
  ((<+>), parens, unwords, unlines)
import Data.String (IsString(..))
import GHC.Builtins (naturalTy)
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

-- | The type level witness of the SMT configuration.
data SMT = SMTConfig

instance (IsString s, Monoid s) => ProverConfig SMT s where
  proverName _ = "SMT"

  -- SMT does not need imports, but we can define some functions to support
  -- operators that are not natively supported by SMT-Lib2.
  operatorImports _ = \case
    NZero -> ""  ;  Add    -> ""
    EqC   -> ""  ;  Sub    -> ""
    LtC   -> ""  ;  Mul    -> ""
    LeC   -> ""  ;  Exp    -> ""
    GtC   -> ""  ;  Div    -> ""
    GeC   -> ""  ;  Mod    -> ""
    EqB   -> ""  ;  FLog   -> ""
    LtB   -> ""  ;  CLogWZ -> ""
    LeB   -> ""  ;  Log2   -> ""
    GtB   -> ""  ;  CLog2  -> ""
    GeB   -> ""  ;  GCD    -> ""
    And   -> ""  ;  LCM    -> ""
    Or    -> ""  ;  FLog2  -> ""
    Not   -> ""  ;  Log    -> ""
    If    -> ""  ;  CLog   -> ""
    Min -> "(define-fun nmin ((a Int) (b Int)) Int (ite (<= a b) a b))"
    Max -> "(define-fun nmax ((a Int) (b Int)) Int (ite (<= a b) b a))"

  printOp _ = \case
    EqB -> "="   ;  LtB -> "<"   ;  LeB -> "<="   ;  GtB   -> ">"
    GeB -> ">="  ;  EqC -> "="   ;  LtC -> "<"    ;  NZero -> "<= 1"
    LeC -> "<="  ;  GtC -> ">"   ;  GeC -> ">="   ;  Min   -> "nmin"
    Add -> "+"   ;  Sub -> "-"   ;  Mul -> "*"    ;  Max   -> "nmax"
    And -> "and" ;  Or  -> "or"  ;  Not -> "not"  ;  If    -> "ite"
    Div -> "div" ;  Mod -> "mod"
    Exp   -> "NO PRIMITIVE" ;  FLog2  -> "NO PRIMITIVE"
    CLog2 -> "NO PRIMITIVE" ;  Log2   -> "NO PRIMITIVE"
    Log   -> "NO PRIMITIVE" ;  CLog   -> "NO PRIMITIVE"
    FLog  -> "NO PRIMITIVE" ;  CLogWZ -> "NO PRIMITIVE"
    GCD   -> "NO PRIMITIVE" ;  LCM    -> "NO PRIMITIVE"

  printBool _ = \case
    True  -> "true"
    False -> "false"

  printTerm p = \case
    Op op `S` t0 `S` t1 `S` t2 -> parens (printOp p op <+> printTerm p t0 <+> printTerm p t1 <+> printTerm p t2)
    Op op `S` t0 `S` t1 -> parens (printOp p op <+> printTerm p t0 <+> printTerm p t1)
    Op op `S` t0 -> parens (printOp p op <+> printTerm p t0)
    t -> defPrintTerm p t

  printSignature p Signature{..} = unlines $
    [parens $ "declare-const" <+> printVar p v <+> sort v | v <- sigVars]
      <> [parens $ "assert" <+> (parens $ "<= 0" <+> printVar p v) | v <- sigVars, isNat v]
      <> [parens $ "assert" <+> (parens $ "not" <+> (parens $ "=>" <+> premise <+> conclusion))]
     where
      andClause = \case
        [] -> "true"
        [t] -> printTerm p t
        tList -> parens ("and" <+> unwords (printTerm p <$> tList))
      premise = andClause sigPremise
      conclusion = andClause sigConclusion
      sort v | isNat v = "Int"
             | otherwise = "Bool"
      isNat v = tyVarKind v `eqType` naturalTy

  verify p env preamble sig@Signature{..} _ = do
    -- Write the assertion to the file
    writeFile (env.dir </> fileName) $ unlines $
      (unpackFS <$> preamble) <>
      [ ""
      ] <>
      [ imp
      | imp <- requiredImports p sig
      , not $ null imp
      ] <>
      [ ""
      , printSignature p sig
      , "(check-sat)"
      ]

    -- Run the assertion in Z3
    findExecutable "z3" >>= \case
      Just smtSolver -> withCurrentDirectory env.dir $ do
        (exitCode, out, err) <- readProcessWithExitCode smtSolver [fileName] ""
        return $ case (exitCode, lines out) of
          (ExitSuccess, "unsat" : _) -> Nothing
          (ExitSuccess, "sat" : _) -> Just "The lemma is false (counterexample found)"
          _ -> Just $ fromString (out <> err)
      Nothing -> return $ Just "Failure: z3 not present on the system."
   where
    fileName = getOccString (getName sigClass) <.> "smt2"

instance ProverFixities SMT where
  bOpFixity _ _ = Fixity 9 InfixL Prefix