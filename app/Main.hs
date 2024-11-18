{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE UndecidableInstances #-}

module Main where

import GHC.TypeLits

import Data.Constraint (Dict (..))
import Unsafe.Coerce (unsafeCoerce)

{- |
 Main entry point.

 `just run` will invoke this function.
-}
main :: IO ()
main = do 
  return ()

{-PrototypeProver test6 proof
  intros.
  apply le_S in H.
  apply le_S_n.
  rewrite <- PeanoNat.Nat.add_0_l at 1.
  rewrite PeanoNat.Nat.add_comm.
  rewrite PeanoNat.Nat.add_succ_l.
  rewrite PeanoNat.Nat.add_comm.
  rewrite <- PeanoNat.Nat.add_succ_l.
  rewrite PeanoNat.Nat.add_comm.
  apply H.
  @-}
test6 :: forall (n :: Nat) (m :: Nat) . (m + 1 <= n) => Dict (m <= n)
test6 = unsafeCoerce ((0 :: Nat) <= 0)
