{-# LANGUAGE TemplateHaskellQuotes #-}
module GHC.TypeNats.Proof.Plugin.Config
  ( PluginConfig(..)
  , pluginName
  , autoProveFlag
  , proofDirFlag
  , verifyProofsFlag
  , optionsParser
  ) where

import Data.Either (partitionEithers)
import Data.List (stripPrefix, dropWhileEnd)
import Data.String (IsString(..))
import GHC.Driver.Plugins (CommandLineOption)

pluginName :: IsString s => s
pluginName = fromString $ g $ g $ show 'pluginName
 where
  g = init . dropWhileEnd (/= '.')

autoProveFlag :: IsString s => s
autoProveFlag = "AutoProve"

proofDirFlag :: IsString s => s
proofDirFlag = "ProofDir"

verifyProofsFlag :: IsString s => s
verifyProofsFlag = "VerifyProofs"

-- | The plugin's command line configuration options.
data PluginConfig = PluginConfig
  { -- | try to automatically apply QED instances in scope
    autoProve :: Bool
    -- | run the prover on the generated files
  , verifyProofs :: Bool
    -- | the folder for saving the proof files
  , proofDir :: FilePath
  }

-- | The configuration defaults.
defaultConfig :: PluginConfig
defaultConfig = PluginConfig
  { autoProve = False
  , verifyProofs = True
  , proofDir = "proofs"
  }

-- | A simple options parser for adjusting the 'defaultConfig'.
optionsParser :: [CommandLineOption] -> Either [CommandLineOption] PluginConfig
optionsParser opts = case partitionEithers $ optionParser <$> opts of
  ([], upds) -> return $ foldl (flip ($)) defaultConfig upds
  (xs,  _) -> Left xs
 where
  optionParser opt
    -- autoProve
    | Just "True" <- stripPrefixEq autoProveFlag opt
    = return $ \c -> c { autoProve = True }
    | Just "False" <- stripPrefixEq autoProveFlag opt
    = return $ \c -> c { autoProve = False }
    -- verifyProofs
    | Just "True" <- stripPrefixEq verifyProofsFlag opt
    = return $ \c -> c { verifyProofs = True }
    | Just "False" <- stripPrefixEq verifyProofsFlag opt
    = return $ \c -> c { verifyProofs = False }
    -- proofDir
    | Just dir <- stripPrefixEq proofDirFlag opt
    = return $ \c -> c { proofDir = dir }
    | otherwise
    = Left opt

  stripPrefixEq x y = stripPrefix x y >>= \case
    '=':xr -> return xr
    _ -> Nothing
