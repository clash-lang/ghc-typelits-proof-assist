{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DoAndIfThenElse #-}

module ProverPlugin (plugin) where

import GHC.Plugins
import GHC.Hs
import Data.Data (Data (..))
import Data.Generics (extQ)
import GHC.Generics (Generic)
import qualified GHC.Data.Strict
import GHC.Data.Maybe (mapMaybe)
import Control.Monad (guard, when)
import Data.List (intersperse, intercalate)
import GHC.Utils.Ppr (Mode(PageMode))
import GHC.IO.Handle.FD (stdout)
import GHC.Builtin.Names (mkUnboundName)
import Data.ByteString.Char8 (unpack)
import Data.Maybe (fromMaybe)
import System.IO (openTempFile, hClose, hPutStr, hFlush)
import System.Process (readProcessWithExitCode)
import System.Exit (ExitCode(..))
import Data.Aeson (FromJSON, ToJSON)
import Data.Bool (bool)
import Data.String (IsString(..))
import GHC.Types.Error (mkPlainError, mkSimpleUnknownDiagnostic, mkMessages)
import GHC.Parser.Errors.Types (PsMessage(..))
import GHC.Utils.Error (mkPlainErrorMsgEnvelope)
import GHC.Data.Bag (listToBag)
import Data.Functor ((<&>))

prototypeProverToken :: String
prototypeProverToken = "{-PrototypeProver"

data Prover = Coq -- | Agda
  deriving Show

data ProofStatement = ProofStatement
  { proofStatementName  :: String
  , proofStatementSig   :: String
  , proofProver         :: Prover
  , proofStatementProof :: String -- Comes from the annotation.
  , proofPreamble       :: String
  } deriving Show

data ProofComment = ProofComment
  { proofCommentName   :: String
  , proofCommentProof  :: String
  , proofCommentProver :: Prover
  } deriving Show

data ProofValidity = Invalid | Valid
  deriving (Show, Generic, FromJSON, ToJSON)

plugin :: Plugin
plugin = defaultPlugin
  { parsedResultAction = analyzeParsedModule
  , driverPlugin = prototypeOptionPlugin
  }

-- To keep the comments in the stream.
prototypeOptionPlugin :: [CommandLineOption] -> HscEnv -> IO HscEnv
prototypeOptionPlugin _ hscEnv = return hscEnv { hsc_dflags = hsc_dflags hscEnv `gopt_set` Opt_KeepRawTokenStream }

analyzeParsedModule :: [CommandLineOption] -> ModSummary -> ParsedResult -> Hsc ParsedResult
analyzeParsedModule cmdOpts ms parsedResult = do
  let hsParsedMod = parsedResultModule parsedResult
      hsMod       = unLoc $ hpm_module hsParsedMod
      -- We retrieve all the declarations, and filter out by <whatever>.
      decls       = map unLoc $ hsmodDecls hsMod
      -- This is taken from Liquid Haskell.
      -- The goal is to extract the comments first, with the locations, and then
      -- match the comments with the signatures.
      go :: forall a. Data a => a -> [LEpaComment]
      go = gmapQr (++) [] go `extQ` (id @[LEpaComment])
      toRealSrc (L a e) = L (RealSrcSpan (anchor a) GHC.Data.Strict.Nothing) e
      comments = go hsMod
      -- First, we'll collect all signatures and transform them.
      sigs = mapMaybe analyzeSignature decls
      parsedComments = mapMaybe parseCommentsForProofs comments
  -- Load the preamble
  preamble <- liftIO $ loadPreamble cmdOpts
  -- Then, we'll only keep the ones that have associated annotations.
  let statements = [sigToStatement preamble sig proofCom | sig <- sigs, proofCom <- parsedComments, sigName sig == proofCommentName proofCom]

  validities <- liftIO $ mapM runProofStatement statements

  if all fst validities then
    return parsedResult
  else do
    let coqErrors = map (mkPlainErrorMsgEnvelope (UnhelpfulSpan UnhelpfulGenerated) .createErrorMessage . snd) validities
    return $ parsedResult {
       parsedResultMessages = (parsedResultMessages parsedResult) {
          psErrors = mkMessages $ listToBag coqErrors
      }
    }

loadPreamble :: [CommandLineOption] -> IO String
loadPreamble [] = return ""
loadPreamble (file:_) = readFile file <&> (++ "\n")

createErrorMessage :: String -> PsError
createErrorMessage = PsUnknownMessage . mkSimpleUnknownDiagnostic . mkPlainError [] . fromString

-- Calls Coq on the given file, returns True if it worked.
callCoq :: FilePath -> IO (Bool, String)
callCoq path = do
  -- We return stderr.
  (exitCode, _, output) <- readProcessWithExitCode "coqc" [path] ""
  return (exitCode == ExitSuccess, output)

-- Runs the Coq proof for a statement.
-- Returns (failure, Coq's stdout) .
runProofStatement :: ProofStatement -> IO (Bool, String)
runProofStatement ps@(ProofStatement {..}) = do
  -- TODO: fetch system's temporary directory in a better way.
  -- Could be given as an argument.
  -- Write the proof to the file
  let path = "/tmp/" ++ proofStatementName ++ ".v"
  let coqProof = statementToCoq ps
  writeFile path coqProof
  -- Run the proof in Coq
  callCoq path

statementToCoq :: ProofStatement -> String
statementToCoq (ProofStatement {..}) =
  proofPreamble ++ "Lemma " ++ proofStatementName ++ " : " ++ proofStatementSig ++ ".\n" ++ proofStatementProof ++ "\nQed.\n"

sigToStatement :: String -> Signature -> ProofComment -> ProofStatement
sigToStatement preamble (Signature {..}) (ProofComment {..})= ProofStatement
  { proofStatementName  = sigName
  , proofStatementSig   = sigType
  , proofProver         = proofCommentProver
  , proofStatementProof = proofCommentProof
  , proofPreamble       = preamble
  }

parseCommentsForProofs :: LEpaComment -> Maybe ProofComment
parseCommentsForProofs (L _ comment) = parseComment comment
  where parseComment com
          | EpaBlockComment str <- ac_tok comment = parseProof str
          | otherwise = Nothing

-- First line is description for the plugin to work, rest is the actual proof.
-- Goes like "<function name> <prover>" on the first line.
-- TODO: Rewrite it in a less hacky manner.
parseProof :: String -> Maybe ProofComment
parseProof com = do
  let len = length def
  guard (len >= 3)
  let isProof:name:prover = def
  guard (isProof == prototypeProverToken)
  -- TODO: Support other provers.
  return $ ProofComment name proof Coq
  where
    def_line:proof' = lines com
    def = words def_line
    proof = unwords (init $ words $ intercalate "\n" proof')

data Signature = Signature
  { sigName :: String
  , sigType :: String
  } deriving Show

analyzeSignature :: HsDecl GhcPs -> Maybe Signature
analyzeSignature (SigD _ sig) = case sig of
  -- We're only interested in type signatures here.
  TypeSig _ ls hsWCBnds -> case ls of
    [] -> Nothing
    (L _ rdrName):_ -> case rdrName of
      -- Only unqualified names, to get the top-level functions.
      Unqual occName -> case hsWCBnds of
        HsWC _ body -> Just $ Signature { sigName = getOccString $ mkUnboundName occName, sigType = transformSignature $ unLoc body }
      _          -> Nothing
  _ -> Nothing
analyzeSignature _ = Nothing

transformSignature :: HsSigType GhcPs -> String
transformSignature sig@(HsSig _ sbndrs body) =
  case sbndrs of
    HsOuterExplicit _ bndrs -> transformForalls (map unLoc bndrs) ++ transformBody (unLoc body)
    _ -> transformBody (unLoc body)

transformForalls :: [HsTyVarBndr f (NoGhcTc GhcPs)] -> String
transformForalls bndrs = "forall " ++ unwords (map transformBinder bndrs) ++ ", "

transformBinder :: HsTyVarBndr f (NoGhcTc GhcPs) -> String
transformBinder bndr = case bndr of
  UserTyVar _ _flag lidp -> getNameFromRdr (unLoc lidp)
  KindedTyVar _ _flag lidp hsType ->
    "{" ++ getNameFromRdr (unLoc lidp) ++ " : " ++ transformBody (unLoc hsType) ++ "}"

transformBody :: HsType GhcPs -> String
transformBody hsType = case hsType of
  -- TODO: take into account the type of arrow.
  -- This is a bit tricky as constraints MIGHT be nested, so we just add parens.
  HsQualTy _ lCtx hsType ->
    let ctx = map unLoc $ unLoc lCtx
    in -- Basically a list of types.
    concatMap ((++ " -> ") . transformBody) ctx ++ transformBody (unLoc hsType)
  HsFunTy _ _arrow t1 t2 -> transformBody (unLoc t1) ++ " -> " ++ transformBody (unLoc t2)
  HsAppTy _ t1 t2 -> transformBody (unLoc t1) ++ " " ++ transformBody (unLoc t2)
  HsTyVar _ _prom lidp -> getNameFromRdr $ unLoc lidp
  HsOpTy _ _prom t1 lidp t2 -> transformBody (unLoc t1) ++ " " ++ getNameFromRdr (unLoc lidp) ++ " " ++ transformBody (unLoc t2)
  HsTupleTy _ _sort tuple -> "(" ++ intercalate ", " (map (transformBody . unLoc) tuple) ++ ")"
  HsParTy _ hsType -> "(" ++ transformBody (unLoc hsType) ++ ")"
  HsTyLit _ hsTyLit -> case hsTyLit of
    HsNumTy _ int  -> show int
    HsStrTy _ fstr -> unpack $ bytesFS fstr
    HsCharTy _ c -> [c]
  -- TODO: add more cases when needed (or better error handling for that matter).
  _ -> undefined

transformedNames :: [(String, String)]
transformedNames = [("Nat", "nat"), ("Dict", "")]

getNameFromRdr :: RdrName -> String
getNameFromRdr rdrName =
  case rdrName of
    Unqual occName ->
      let name = getOccString $ mkUnboundName occName in
       fromMaybe name $ lookup name transformedNames
    _ -> ""

