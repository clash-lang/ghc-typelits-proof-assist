module GHC.TypeNats.Proof.Plugin.Prover
  ( Prover(..)
  , module GHC.TypeNats.Proof.Plugin.Prover.Tynal
  ) where

import Data.String (IsString(..))
import GHC.Data.FastString (mkFastString)
import GHC.Utils.Outputable (Outputable(..))
import GHC.Types.Unique (Uniquable(..))

import GHC.TypeNats.Proof.Plugin.Prover.Agda
import GHC.TypeNats.Proof.Plugin.Prover.Coq
import GHC.TypeNats.Proof.Plugin.Prover.Tynal

-- | Supported proof assistants.
data Prover
  = Coq  -- ^ <https://coq.inria.fr>
  | Agda -- ^ <https://github.com/agda/agda>
  deriving (Eq, Ord, Show, Read, Enum, Bounded)

-- | A dedicated 'ProverConfig' dictionary type.
data HasProverConfig s = forall p. ProverConfig p s => HasCfg p

-- | Connects a 'Prover' with a corresponding 'ProverConfig'.
hasConfig :: (IsString s, Monoid s) => Prover -> HasProverConfig s
hasConfig = \case
  Coq  -> HasCfg CoqConfig
  Agda -> HasCfg AgdaConfig

instance Outputable Prover where
  ppr = ppr . mkFastString . show

instance Uniquable Prover where
  getUnique = getUnique . fromEnum

instance (IsString s, Monoid s) => ProverConfig Prover s where
  proverName p      | HasCfg c <- hasConfig @s p = proverName c
  operatorImports p | HasCfg c <- hasConfig @s p = operatorImports c
  printLit p        | HasCfg c <- hasConfig @s p = printLit c
  printVar p        | HasCfg c <- hasConfig @s p = printVar c
  printOp p         | HasCfg c <- hasConfig @s p = printOp c
  printSignature p  | HasCfg c <- hasConfig @s p = printSignature c
  verify p          | HasCfg c <- hasConfig @s p = verify c

instance ProverFixities Prover where
  bOpFixity p | HasCfg c <- hasConfig @String p = bOpFixity c
