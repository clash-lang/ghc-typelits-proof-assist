{-# OPTIONS_GHC -fplugin=GHC.TypeNats.Proof.Plugin #-}
{-# OPTIONS_GHC -fplugin-opt=GHC.TypeNats.Proof.Plugin:AutoProve=True #-}

module Intro where

import GHC.TypeNats
import GHC.TypeNats.Proof

import Intro.CoqProof
--import Intro.AgdaProof

usingRewrite :: forall n m. (n + 1 <= m) => SNat n -> SNat m -> Int
usingRewrite | Rewrite <- using @(Lemma n m) = demand

usingApply :: forall n m. (n + 1 <= m) => SNat n -> SNat m -> Int
usingApply = apply @(Lemma n m) demand

usingAuto :: forall n m. (n + 1 <= m) => SNat n -> SNat m -> Int
usingAuto = demand

demand :: n <= m => SNat n -> SNat m -> Int
demand _ _ = 3
