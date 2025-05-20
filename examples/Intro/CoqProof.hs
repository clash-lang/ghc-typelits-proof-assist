{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}

{-# OPTIONS_GHC -fplugin=GHC.TypeNats.Proof.Plugin #-}

{-/ Preamble (Coq):
Require Import Coq.Arith.PeanoNat.
/-}
module Intro.CoqProof where

import GHC.TypeNats
import GHC.TypeNats.Proof

instance
  ( n + 1 <= m
  ) => Lemma n m
class -- =>
  ( n <= m
  ) => Lemma n m
{-/ Proof (Coq): Lemma
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
/-}
instance Lemma n m => QED (Lemma n m)
