{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}

{-# OPTIONS_GHC -fplugin=GHC.TypeNats.Proof.Plugin #-}

{-/ Preamble (Agda):
open import Data.Nat.Properties using (+-comm; m+1+n≰m)
open import Relation.Nullary.Negation using (contradiction)
/-}
module Intro.AgdaProof where

import GHC.TypeNats
import GHC.TypeNats.Proof

instance
  ( n + 1 <= m
  ) => Lemma n m
class -- =>
  ( n <= m
  ) => Lemma n m
{-/ Proof (Agda): Lemma
Lemma n zero p rewrite +-comm n 1 = contradiction (m+1+n≰m 0) λ x -> x p
Lemma zero (suc m) p = z≤n
Lemma (suc n) (suc m) p = s≤s (Lemma n m (s≤s⁻¹ p))
/-}
instance Lemma n m => QED (Lemma n m)
