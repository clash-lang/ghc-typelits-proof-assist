{-# LANGUAGE Safe #-}
{-# LANGUAGE NoGeneralizedNewtypeDeriving #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}

module Test.GHC.TypeNats.Proof.Plugin.Coq where

import GHC.TypeNats.Proof

{-/ Preamble (Coq):
Require Import Coq.Arith.PeanoNat.
/-}

instance T0 n
class
  ( 2 * n ~ n + n
  ) => T0 n
{-/ Proof (Coq): T0
  intros n.
  destruct n.
  reflexivity.
  rewrite !Nat.mul_succ_l.
  rewrite Nat.mul_0_l.
  rewrite Nat.add_0_l.
  reflexivity.
/-}
instance T0 n => QED (T0 n)

instance T1 n
class
  ( 2 * n - n ~ n
  ) => T1 n
{-/ Proof (Coq): T1
  intros.
  rewrite !Nat.mul_succ_l.
  apply Nat.add_sub.
/-}
instance T1 n => QED (T1 n)

instance T2 n
class
  ( n `Div` 2 <= n
  ) => T2 n
{-/ Proof (Coq): T2
  intros.
  apply Nat.Div0.div_le_upper_bound.
  rewrite !Nat.mul_succ_l.
  apply Nat.le_add_l.
/-}
instance T2 n => QED (T2 n)

instance T3 n
class
  ( n `Mod` 2 < 2
  ) => T3 n
{-/ Proof (Coq): T3
  intros.
  apply Nat.mod_upper_bound.
  apply Nat.neq_succ_0.
/-}
instance T3 n => QED (T3 n)

instance T4 n
class
  ( 2 ^ n > 0
  ) => T4 n
{-/ Proof (Coq): T4
  intros.
  induction n as [| n IH].
  - simpl. apply Nat.lt_0_1.
  - rewrite Nat.pow_succ_r. rewrite !Nat.mul_succ_l.
    simpl.
    apply Nat.add_pos_pos.
    apply IH. apply IH.
    apply Nat.le_0_l.
/-}
instance T4 n => QED (T4 n)

instance
  ( m >= n
  ) => T5 m n
class
  ( Max m n ~ m
  ) => T5 m n
{-/ Proof (Coq): T5
  intros.
  apply Nat.max_l.
  apply H.
/-}
instance T5 m n => QED (T5 m n)

instance
  ( m <= n
  ) => T6 m n
class
  ( Min m n ~ m
  ) => T6 m n
{-/ Proof (Coq): T6
  intros.
  apply Nat.min_l.
  apply H.
/-}
instance T6 m n => QED (T6 m n)

instance T7 m n
class
  ( GCD (2 * m) (2 * n) `Div` 2 ~ GCD m n
  ) => T7 m n
{-/ Proof (Coq): T7
  intros.
  rewrite Nat.gcd_mul_mono_l.
  rewrite Nat.mul_comm.
  rewrite Nat.div_mul.
  reflexivity.
  apply Nat.neq_succ_0.
/-}
instance T7 m n => QED (T7 m n)

instance T8 m n
class
  ( LCM (2 * m) (2 * n) ~ 2 * LCM m n
  ) => T8 m n
{-/ Proof (Coq): T8
  intros.
  apply Nat.lcm_mul_mono_l.
/-}
instance T8 m n => QED (T8 m n)

instance T9 n
class
  ( Log2 (2 ^ n) ~ n
  ) => T9 n
{-/ Proof (Coq): T9
  intros.
  apply Nat.log2_pow2.
  apply Nat.le_0_l.
/-}
instance T9 n => QED (T9 n)

instance T10 n
class
  ( FLog2 (2 ^ n) ~ n
  ) => T10 n
{-/ Proof (Coq): T10
  intros.
  apply Nat.log2_pow2.
  apply Nat.le_0_l.
/-}
instance T10 n => QED (T10 n)

instance T11 n
class
  ( FLog 2 (2 ^ n) ~ n
  ) => T11 n
{-/ Proof (Coq): T11
  intros.
  apply Nat.log2_pow2.
  apply Nat.le_0_l.
/-}
instance T11 n => QED (T11 n)

instance
  ( 1 <= n
  ) => T12 n
class
  ( 0 `Mod` n ~ 0
  ) => T12 n
{-/ Proof (Coq): T12
  intros.
  apply Nat.Div0.mod_0_l.
/-}
instance T12 n => QED (T12 n)

instance
  ( 1 <= n
  ) => T13 n
class
  ( If ((False && True) || Not False) (0 `Mod` n) 3 ~ 0
  ) => T13 n
{-/ Proof (Coq): T13
  intros.
  apply Nat.Div0.mod_0_l.
/-}
instance T13 n => QED (T13 n)

instance
  ( a <= b, b <= c
  ) => T14 a b c
class
  ( a <= c
  ) => T14 a b c
{-/ Proof (Coq): T14
  intros a b c H0 H1.
  apply (Nat.le_trans a b c H0 H1).
/-}
instance T14 a b c => QED (T14 a b c)
