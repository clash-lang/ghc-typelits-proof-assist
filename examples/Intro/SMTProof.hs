{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}

{-# OPTIONS_GHC -fplugin=GHC.TypeNats.Proof.Plugin #-}

{-/ Preamble (SMT):
(set-logic QF_LIA)
/-}
module Intro.SMTProof where

import GHC.TypeNats
import GHC.TypeNats.Proof

instance
  ( n + 1 <= m
  ) => Lemma n m
class -- =>
  ( n <= m
  ) => Lemma n m
{-/ Proof (SMT): Lemma/-}
instance Lemma n m => QED (Lemma n m)
