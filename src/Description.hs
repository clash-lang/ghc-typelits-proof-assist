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
  { proofExpression :: Expression
  , proofFile       :: Maybe FilePath
  , proofValidity   :: ProofValidity
  } deriving (Generic, Show, FromJSON, ToJSON)

createProofToken :: Expression -> ProofToken
createProofToken expr = ProofToken
  { proofExpression = expr
  , proofFile       = Nothing
  , proofValidity   = Invalid
  }

isProofValid :: ProofToken -> Bool
isProofValid (ProofToken { proofValidity = proofValidity }) =
  case proofValidity of
    Invalid -> False
    Valid _ -> True

createProofTokenWithFile :: NatEq -> IO ProofToken
createProofTokenWithFile natEq = do
  let expr  = natEqToCoq natEq
      title = drop 56 $ T.unpack $ T.decodeASCII (Base16.encode $ SHA256.hash $ T.encodeUtf8 $ T.pack expr)
      lemma = natEqToCoqLemma title natEq
      file  = title ++ ".v"
      token = (createProofToken expr) { proofFile = Just file }
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
  return $ T.unpack $ T.decodeASCII $ Base16.encode $ SHA256.hash proofFile

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
  deriving (Show, Eq)

data NatEq = NatEq NatExpression NatExpression deriving Eq

-- * Transforming expression into Coq code.


-- Takes a NatExpression and transforms it into a Coq expression.
natExprToCoq :: NatExpression -> String
natExprToCoq (NatVar s) = s
natExprToCoq (NatLit n) = show n
natExprToCoq (NatAdd e1 e2) = natExprToCoq e1 ++ " + " ++ natExprToCoq e2
natExprToCoq (NatMul e1 e2) = natExprToCoq e1 ++ " * " ++ natExprToCoq e2

natEqToCoq :: NatEq -> String
natEqToCoq (NatEq e1 e2) = natExprToCoq e1 ++ " = " ++ natExprToCoq e2

variablesFromNatExpr :: NatExpression -> [NatVariable]
variablesFromNatExpr (NatVar s) = [s]
variablesFromNatExpr (NatAdd e1 e2) = variablesFromNatExpr e1 ++ variablesFromNatExpr e2
variablesFromNatExpr (NatMul e1 e2) = variablesFromNatExpr e1 ++ variablesFromNatExpr e2
variablesFromNatExpr _ = []

-- Get the set of variables used in an equivalence over naturals.
variablesFromNatEq :: NatEq -> [NatVariable]
variablesFromNatEq (NatEq e1 e2) = ordNub $ variablesFromNatExpr e1 ++ variablesFromNatExpr e2

-- TODO: Rewrite it with a proper string builder
natEqToCoqLemma :: String -> NatEq -> String
natEqToCoqLemma title natEq =
  "Lemma " ++ title ++ " : forall " ++ unwords vars ++ " : nat, " ++ expr ++ "." ++ "\nauto.\nQed."
  where vars = variablesFromNatEq natEq
        expr = natEqToCoq natEq

