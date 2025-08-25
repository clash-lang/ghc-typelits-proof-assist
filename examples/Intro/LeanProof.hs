{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}

{-# OPTIONS_GHC -fplugin=GHC.TypeNats.Proof.Plugin #-}

module Intro.LeanProof where

import GHC.TypeNats
import GHC.TypeNats.Proof

instance
  ( n + 1 <= m
  ) => Lemma n m
class -- =>
  ( n <= m
  ) => Lemma n m
{-/ Proof (Lean): Lemma
  exact Nat.pred_le_pred ∘ Nat.le.step
/-}

instance Lemma n m => QED (Lemma n m)
