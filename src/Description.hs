{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DoAndIfThenElse #-}
{-# LANGUAGE PatternGuards #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

module Description where

import Data.Aeson
import Data.Time (UTCTime)
import GHC.Generics (Generic)
import qualified Data.ByteString as BS
import qualified Crypto.Hash.SHA256 as SHA256
import qualified Data.Text as T
import qualified Data.Text.Encoding as T
import System.Exit (ExitCode(..))
import System.Process (readProcessWithExitCode)
import qualified Data.ByteString.Base16 as Base16
import GHC.Natural (Natural)
import GHC.Plugins (ordNub)
import Data.Bool (bool)

data ProofValidity = Invalid | Valid String
  deriving (Show, Generic, FromJSON, ToJSON)

type Expression = String

data ProofToken = ProofToken
  { proofExpressionGiven  :: [Expression]
  , proofExpressionWanted :: Expression
  , proofFile             :: Maybe FilePath
  , proofValidity         :: ProofValidity
  } deriving (Generic, Show, FromJSON, ToJSON)

createProofToken :: [Expression] -> Expression -> ProofToken
createProofToken gExprs wExpr = ProofToken
  { proofExpressionGiven  = gExprs
  , proofExpressionWanted = wExpr
  , proofFile             = Nothing
  , proofValidity         = Invalid
  }

isProofValid :: ProofToken -> Bool
isProofValid (ProofToken { proofValidity = proofValidity }) =
  case proofValidity of
    Invalid -> False
    Valid _ -> True

computeHash :: BS.ByteString -> String
computeHash = T.unpack . T.decodeASCII . Base16.encode . SHA256.hash

createProofTokenWithFile :: [NatEq] -> NatEq -> IO ProofToken
createProofTokenWithFile givenNatEqs wantedNatEq = do
  let wExpr  = natEqToCoq wantedNatEq
      gExprs = map natEqToCoq givenNatEqs
      -- We keep only 8 bytes from the hash for the name of the lemma.
      -- TODO: Find the best way to manage hashes.
      -- Token at the beginning to avoid starting with a number.
      title = "f" ++ drop 56 (computeHash $ T.encodeUtf8 $ T.pack $ wExpr ++ concat gExprs)
      lemma = natEqToCoqLemma title givenNatEqs wantedNatEq
      file  = title ++ ".v"
      token = (createProofToken gExprs wExpr) { proofFile = Just file }
  writeFile file lemma
  return token

loadDescriptionFile :: FilePath -> IO (Maybe [ProofToken])
loadDescriptionFile = decodeFileStrict

-- Calls Coq on the given file, returns True if it worked.
callCoq :: FilePath -> IO Bool
callCoq path = do
  -- TODO: Manage Coq's output to present it to the user.
  -- Ignore stdout and stderr.
  (exitCode, _, _) <- readProcessWithExitCode "coqc" [path] ""
  return $ exitCode == ExitSuccess

computeHashFromFile :: FilePath -> IO String
computeHashFromFile path = do
  proofFile <- BS.readFile path
  return $ computeHash proofFile

runProof :: ProofToken -> IO ProofValidity
runProof token
  | Nothing   <- proofFile token = return Invalid
  | Just path <- proofFile token, validity@(Valid oldHash) <- proofValidity token = do
      newHash <- computeHashFromFile path
      if oldHash == newHash then
        return validity -- Nothing changed.
      else do
        coqResult <- callCoq path
        return $ bool Invalid (Valid newHash) coqResult
  | Just path <- proofFile token, Invalid <- proofValidity token = do
      newHash <- computeHashFromFile path
      coqResult <- callCoq path
      return $ bool Invalid (Valid newHash) coqResult

checkProofToken :: ProofToken -> IO ProofToken
checkProofToken token = do
  validity <- runProof token
  return $ token { proofValidity = validity }

-- * Bulding a structure to represent expressions on naturals.

type NatVariable = String

data NatExpression =
  NatVar NatVariable
  | NatLit Natural
  | NatAdd NatExpression NatExpression
  | NatMul NatExpression NatExpression
  | NatExp NatExpression NatExpression
  | NatSub NatExpression NatExpression
  | NatDiv NatExpression NatExpression
  | NatMod NatExpression NatExpression
  | NatCon String [NatExpression]
  deriving (Show, Eq)

data NatEq =
  NatEq NatExpression NatExpression
  | NatInEq NatExpression NatExpression -- Only <= atm.
  deriving Eq

-- * Transforming expression into Coq code.
-- TODO: Make the architecture more modular, to incorporate other provers as well.

-- Takes a NatExpression and transforms it into a Coq expression.
natExprToCoq :: NatExpression -> String
natExprToCoq (NatVar s) = s
natExprToCoq (NatLit n) = show n
natExprToCoq (NatAdd e1 e2) = "(" ++ natExprToCoq e1 ++ " + " ++ natExprToCoq e2 ++ ")"
natExprToCoq (NatMul e1 e2) = "(" ++ natExprToCoq e1 ++ " * " ++ natExprToCoq e2 ++ ")"
-- TODO: This is contingent on "Require Import Nat.".
natExprToCoq (NatExp e1 e2) = "(" ++ natExprToCoq e1 ++ " ^ " ++ natExprToCoq e2 ++ ")"
natExprToCoq (NatSub e1 e2) = "(" ++ natExprToCoq e1 ++ " - " ++ natExprToCoq e2 ++ ")"
natExprToCoq (NatDiv e1 e2) = "(" ++ natExprToCoq e1 ++ " / " ++ natExprToCoq e2 ++ ")"
natExprToCoq (NatMod e1 e2) = "(" ++ natExprToCoq e1 ++ " % " ++ natExprToCoq e2 ++ ")"
natExprToCoq (NatCon name exps) = "(" ++ name ++ concatMap ((" " ++) . natExprToCoq) exps ++ ")"

natEqToCoq :: NatEq -> String
natEqToCoq (NatEq e1 e2) = natExprToCoq e1 ++ " = " ++ natExprToCoq e2
natEqToCoq (NatInEq e1 e2) = natExprToCoq e1 ++ " <= " ++ natExprToCoq e2

-- TODO: We might as well get the variables from the available skolems.
variablesFromNatExpr :: NatExpression -> [NatVariable]
variablesFromNatExpr (NatVar s) = [s]
variablesFromNatExpr (NatAdd e1 e2)  = variablesFromNatExpr e1 ++ variablesFromNatExpr e2
variablesFromNatExpr (NatMul e1 e2)  = variablesFromNatExpr e1 ++ variablesFromNatExpr e2
variablesFromNatExpr (NatExp e1 e2)  = variablesFromNatExpr e1 ++ variablesFromNatExpr e2
variablesFromNatExpr (NatSub e1 e2)  = variablesFromNatExpr e1 ++ variablesFromNatExpr e2
variablesFromNatExpr (NatDiv e1 e2)  = variablesFromNatExpr e1 ++ variablesFromNatExpr e2
variablesFromNatExpr (NatMod e1 e2)  = variablesFromNatExpr e1 ++ variablesFromNatExpr e2
variablesFromNatExpr (NatCon _ exps) = concatMap variablesFromNatExpr exps
variablesFromNatExpr _ = []

-- Get the set of variables used in an equivalence over naturals.
variablesFromNatEq :: NatEq -> [NatVariable]
variablesFromNatEq (NatEq e1 e2) = ordNub $ variablesFromNatExpr e1 ++ variablesFromNatExpr e2
variablesFromNatEq (NatInEq e1 e2) = ordNub $ variablesFromNatExpr e1 ++ variablesFromNatExpr e2

-- TODO: Rewrite it with a proper string builder
natEqToCoqLemma :: String -> [NatEq] -> NatEq -> String
natEqToCoqLemma title givenNatEqs wantedNatEq =
  "Lemma " ++ title ++ " : forall " ++ unwords vars ++ " : nat, "
  ++ concatMap givenNatEqToCoq givenNatEqs
  ++ wExpr ++ "." ++ "\nauto.\nQed."
  where vars = variablesFromNatEq wantedNatEq
        wExpr = natEqToCoq wantedNatEq

givenNatEqToCoq :: NatEq -> String
givenNatEqToCoq givenNatEq = natEqToCoq givenNatEq ++ " -> "
