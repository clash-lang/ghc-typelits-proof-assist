{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}

module Test.GHC.TypeNats.Proof.Plugin.Lean where

import GHC.TypeNats.Proof

instance T0 n
class
  ( 2 * n ~ n + n
  ) => T0 n
{-/ Proof (Lean): T0
  rw [Nat.mul_comm]
  exact Nat.mul_two _
/-}
instance T0 n => QED (T0 n)

instance T1 n
class
  ( 2 * n - n ~ n
  ) => T1 n
{-/ Proof (Lean): T1
  rw [Nat.mul_comm, Nat.mul_two, Nat.add_sub_cancel]
/-}
instance T1 n => QED (T1 n)

instance T2 n
class
  ( n `Div` 2 <= n
  ) => T2 n
{-/ Proof (Lean): T2
  exact Nat.div_le_self _ _
/-}
instance T2 n => QED (T2 n)

instance T3 n
class
  ( n `Mod` 2 < 2
  ) => T3 n
{-/ Proof (Lean): T3
  exact Nat.mod_lt n (by decide)
/-}
instance T3 n => QED (T3 n)

instance T4 n
class
  ( 2 ^ n > 0
  ) => T4 n
{-/ Proof (Lean): T4
  apply Nat.pow_pos; simp
/-}
instance T4 n => QED (T4 n)

instance
  ( m >= n
  ) => T5 m n
class
  ( Max m n ~ m
  ) => T5 m n
{-/ Proof (Lean): T5
  rw [Nat.max_def, ite_eq_right_iff]
  exact Nat.le_antisymm
/-}
instance T5 m n => QED (T5 m n)

instance
  ( m <= n
  ) => T6 m n
class
  ( Min m n ~ m
  ) => T6 m n
{-/ Proof (Lean): T6
  intro m_le
  rw [Nat.min_def, ite_eq_left_iff]
  intro n_m_le
  exact (n_m_le m_le).elim
/-}
instance T6 m n => QED (T6 m n)

instance T7 m n
class
  ( GCD (2 * m) (2 * n) `Div` 2 ~ GCD m n
  ) => T7 m n
{-/ Proof (Lean): T7
  rw [Nat.gcd_mul_left]; simp
/-}
instance T7 m n => QED (T7 m n)

instance T8 m n k
class
  ( LCM (LCM m n) k ~ LCM m (LCM n k)
  ) => T8 m n k
{-/ Proof (Lean): T8
  apply Nat.lcm_assoc
/-}
instance T8 m n k => QED (T8 m n k)

instance T9 n
class
  ( Log2 (2 ^ n) ~ n
  ) => T9 n
{-/ Proof (Lean): T9
  simp
/-}
instance T9 n => QED (T9 n)

instance T10 n
class
  ( FLog2 (2 ^ n) ~ n
  ) => T10 n
{-/ Proof (Lean): T10
  simp
/-}
instance T10 n => QED (T10 n)

instance T11 n
class
  ( CLog 2 (2 ^ n) ~ n
  ) => T11 n
{-/ Proof (Lean): T11
  exact Nat.clog_pow 2 n (hb := by decide)
/-}
instance T11 n => QED (T11 n)

instance
  ( 1 <= n
  ) => T12 n
class
  ( 0 `Mod` n ~ 0
  ) => T12 n
{-/ Proof (Lean): T12
  simp
/-}
instance T12 n => QED (T12 n)

instance
  ( NonZero n
  ) => T13 n
class
  ( n `Div` n ~ 1
  ) => T13 n
{-/ Proof (Lean): T13
  exact Nat.div_self ∘ Nat.zero_lt_of_ne_zero ∘ Ne.symm
/-}
instance T13 n => QED (T13 n)

instance
  ( n <= m
  ) => T14 b n m
class
  ( FLog b n <= FLog b m
  ) => T14 b n m
{-/ Proof (Lean): T14
  apply Nat.log_monotone
/-}
instance T14 b n m => QED (T14 b n m)

instance
  ( 1 <= n
  , 1 <= d
  ) => T15 n d
class
  ( 1 <= (n + (d - 1)) `Div` d
  ) => T15 n d
{-/ Proof (Lean): T15
  -- also solved by grind but let's do a non-trivial proof
  intro n_positive d_positive
  cases n with
  | zero =>
      exfalso
      exact n_positive (Eq.refl 0)
  | succ n =>
      have rule : (n + 1 + (d - 1)) / d = n / d + 1 := by
        calc (n + 1 + (d - 1)) / d
          _ = (n + (1 + (d - 1))) / d := by simp only [Nat.add_assoc]
          _ = (n + (d - 1 + 1)) / d   := by simp only [Nat.add_comm]
          _ = (n + d) / d             := by
            cases d with
            | zero   => exfalso; exact d_positive (Eq.refl 0)
            | succ d => simp only [Nat.add_one_sub_one]
          _ = n / d + 1 := Nat.add_div_right n (Nat.zero_lt_of_ne_zero d_positive.symm)
      rw [rule]
      apply Nat.zero_ne_add_one
/-}
instance T15 n d => QED (T15 n d)

instance
  ( 1 <= n
  ) => T16 n
class
  ( If ((False && True) == True || Not False) (0 `Mod` n) 3 ~ 0
  ) => T16 n
{-/ Proof (Lean): T16
  simp [Nat.zero_mod]
/-}
instance T16 n => QED (T16 n)
