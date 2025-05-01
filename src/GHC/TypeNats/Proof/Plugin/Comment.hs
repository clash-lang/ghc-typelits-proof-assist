module GHC.TypeNats.Proof.Plugin.Comment
  ( ProofComment(..)
  , getProofComments
  ) where

import Prelude hiding ((<>))

import Data.Char (isSpace, isUpper, isAlphaNum)
import Data.Data (Data(..))
import Data.Either (partitionEithers)
import Data.List (stripPrefix)
import Data.Maybe (fromMaybe, mapMaybe)
import Data.Monoid (First(..))
import Data.Typeable (Typeable, cast)
import GHC.Data.FastString (FastString, mkFastString)
import GHC.Parser.Annotation
  ( EpaComment(..), EpaCommentTok(..), HasLoc(..), LEpaComment
  , noCommentsToEpaLocation
  )
import GHC.Types.SrcLoc (SrcSpan, unLoc, getLoc)
import GHC.Types.Unique.FM (listToUFM, adjustUFM, lookupUFM)
import GHC.Utils.Outputable (Outputable(..), (<>), (<+>))

import GHC.TypeNats.Proof.Plugin.Prover (Prover(..))

-- | The data that is extracted from the proof comments in the Haskell
-- sources.
data ProofComment name = ProofComment
  { -- | the proof name
    pcName     :: name
  , -- | the proof itself
    pcProof    :: FastString
  , -- | the proof assistant to be used for checking the proof
    pcProver   :: Prover
  , -- | the source location of the proof
    pcLocation :: SrcSpan
  , -- | a potential preamble to be added to the proof
    pcPreamble :: [FastString]
  }

instance Outputable name => Outputable (ProofComment name) where
  ppr ProofComment{..} =
    "{-/ Proof (" <> ppr pcProver <> "):" <+> ppr pcName
      <+> "... /-}" <+> "@" <> ppr pcLocation

-- | The goal is to extract the comments first (with the locations) to
-- match them with the signatures later.
getProofComments :: Data a => a -> [ProofComment FastString]
getProofComments = inline . partitionEithers . mapMaybe parseComments . lepaComments
 where
  inline (xs, pcs) = upd <$> pcs
   where
    ufm0 = listToUFM $ (, []) <$> [minBound .. maxBound]
    ufm1 = foldr (\(p, f) u -> adjustUFM (f:) u p) ufm0 xs
    upd pc = pc { pcPreamble = fromMaybe [] $ lookupUFM ufm1 $ pcProver pc }

  parseComments ::
    LEpaComment ->
    Maybe (Either (Prover, FastString) (ProofComment FastString))
  parseComments lepaComment
    | EpaComment{..} <- unLoc lepaComment
    , EpaBlockComment str <- ac_tok
    , loc <- getHasLoc $ noCommentsToEpaLocation $ getLoc lepaComment
    = parseComment loc str

    | otherwise
    = Nothing

  -- we could make use of a fully fledged parser package at this
  -- point, but our requirements are so simple that we go with a poor
  -- mans parser instead to save on the dependency fingerprint
  parseComment ::
    SrcSpan ->
    String ->
    Maybe (Either (Prover, FastString) (ProofComment FastString))
  parseComment pcLocation s0
    | Just s1 <- stripPrefix "{-/ Proof (" s0
    , Just (')':':':s2, pcProver) <- proverParser s1
    , x:s3 <- dropWhile isSpace s2
    , isUpper x
    , (xr, s4) <- span isAlphaNum s3
    , let pcName = mkFastString (x:xr)
    , let s5 = dropWhile (`elem` (" \t\v" :: String)) s4
    , let s6 = dropWhile (`elem` ("\n\r" :: String)) s5
    , Just s7 <- stripSuffixAndSpace "/-}" s6
    , let pcProof = mkFastString s7
    , let pcPreamble = []
    = Just $ Right ProofComment{..}
  parseComment _ s0
    | Just s1 <- stripPrefix "{-/ Preamble (" s0
    , Just (')':':':s2, prover) <- proverParser s1
    , let s3 = dropWhile isSpace s2
    , Just preamble <- stripSuffixAndSpace "/-}" s3
    = Just $ Left (prover, mkFastString preamble)
  parseComment _ _ = Nothing

  stripSuffixAndSpace sfx s0
    | s1 <- reverse s0
    , Just s2 <- stripPrefix (reverse sfx) s1
    , s3 <- dropWhile isSpace s2
    , s4 <- reverse s3
    = Just s4
  stripSuffixAndSpace _ _ = Nothing

  proverParser :: String -> Maybe (String, Prover)
  proverParser s = getFirst $ mconcat
    [ First $ (, p) <$> stripPrefix (show p) s
    | p <- [minBound .. maxBound]
    ]

  -- This is taken from Liquid Haskell.
  lepaComments :: forall a. Data a => a -> [LEpaComment]
  lepaComments = gmapQr (++) [] lepaComments `extQ` (id @[LEpaComment])

  -- This is taken from the syb package.
  extQ ::
    forall a b r. (Typeable a, Typeable b) =>
    (a -> r) -> (b -> r) -> a -> r
  extQ f g a = maybe (f a) g (cast a)
