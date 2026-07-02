{-# LANGUAGE Safe #-}
{-# LANGUAGE NoGeneralizedNewtypeDeriving #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}

module Test.GHC.TypeNats.Proof.Plugin.Agda where

import GHC.TypeNats.Proof

{-/ Preamble (Agda):
open import Relation.Binary.PropositionalEquality.Core
open import Data.Nat.Properties
open import Data.Nat.Base
open import Data.Nat.DivMod
/-}

instance T0 n
class
  ( 2 * n ~ n + n
  ) => T0 n
{-/ Proof (Agda): T0
T0 zero = refl
T0 (suc n) = cong suc (cong (n +_) (cong suc (+-comm n zero)))
/-}
instance T0 n => QED (T0 n)

instance T1 n
class
  ( 2 * n - n ~ n
  ) => T1 n
{-/ Proof (Agda): T1
T1 n
  rewrite +-comm n zero
  rewrite +-∸-comm {n} n {n} ≤-refl
  rewrite n∸n≡0 n
  = refl
/-}
instance T1 n => QED (T1 n)

instance T2 n
class
  ( n `Div` 2 <= n
  ) => T2 n
{-/ Proof (Agda): T2
T2 n = m/n≤m n 2
/-}
instance T2 n => QED (T2 n)

instance T3 n
class
  ( n `Mod` 2 < 2
  ) => T3 n
{-/ Proof (Agda): T3
T3 n = m%n<n n 2
/-}
instance T3 n => QED (T3 n)

instance T4 n
class
  ( 2 ^ n > 0
  ) => T4 n
{-/ Proof (Agda): T4
T4 n = m^n>0 2 n
/-}
instance T4 n => QED (T4 n)

instance
  ( m >= n
  ) => T5 m n
class
  ( Max m n ~ m
  ) => T5 m n
{-/ Proof (Agda): T5
T5 m n = m≥n⇒m⊔n≡m {m} {n}
/-}
instance T5 m n => QED (T5 m n)

instance
  ( m <= n
  ) => T6 m n
class
  ( Min m n ~ m
  ) => T6 m n
{-/ Proof (Agda): T6
T6 m n = m≤n⇒m⊓n≡m {m} {n}
/-}
instance T6 m n => QED (T6 m n)

instance T7 m n
class
  ( GCD (2 * m) (2 * n) `Div` 2 ~ GCD m n
  ) => T7 m n
{-/ Proof (Agda): T7
T7 m n = gcd[cm,cn]/c≡gcd[m,n] 2 m n
/-}
instance T7 m n => QED (T7 m n)

instance T8 m n
class
  ( GCD m n * LCM m n ~ m * n
  ) => T8 m n
{-/ Proof (Agda): T8
T8 = gcd*lcm
/-}
instance T8 m n => QED (T8 m n)

instance T9 n
class
  ( Log2 (2 ^ n) ~ n
  ) => T9 n
{-/ Proof (Agda): T9
T9 = ⌊log₂[2^n]⌋≡n
/-}
instance T9 n => QED (T9 n)

instance T10 n
class
  ( FLog2 (2 ^ n) ~ n
  ) => T10 n
{-/ Proof (Agda): T10
T10 = ⌊log₂[2^n]⌋≡n
/-}
instance T10 n => QED (T10 n)

instance T11 n
class
  ( FLog 2 (2 ^ n) ~ n
  ) => T11 n
{-/ Proof (Agda): T11
T11 = ⌊log₂[2^n]⌋≡n
/-}
instance T11 n => QED (T11 n)

instance T12 n
class
  ( CLog2 (2 ^ n) ~ n
  ) => T12 n
{-/ Proof (Agda): T12
T12 = ⌈log₂2^n⌉≡n
/-}
instance T12 n => QED (T12 n)

instance T13 n
class
  ( CLog 2 (2 ^ n) ~ n
  ) => T13 n
{-/ Proof (Agda): T13
T13 = ⌈log₂2^n⌉≡n
/-}
instance T13 n => QED (T13 n)

instance
  ( 1 <= n
  ) => T14 n
class
  ( 0 `Mod` n ~ 0
  ) => T14 n
{-/ Proof (Agda): T14
T14 (suc _) = refl
/-}
instance T14 n => QED (T14 n)

instance
  ( 1 <= n
  ) => T15 n
class
  ( If ((False && True) || Not False) (0 `Mod` n) 3 ~ 0
  ) => T15 n
{-/ Proof (Agda): T15
T15 (suc _) = refl
/-}
instance T15 n => QED (T15 n)

instance
  ( 2 <= n
  ) => T16 n
class
  ( 1 <= CLogWZ 2 n 0
  ) => T16 n
{-/ Proof (Agda): T16
open import Relation.Nullary.Negation.Core using (contradiction)
open import Data.Nat.Properties using (m+1+n≰m; ≤-trans; n≤1+n)
T16 (suc n) 2≤n = >-nonZero (lemma (suc n) 2≤n)
 where
  lemma : (n : ℕ) → 2 ≤ n → 1 ≤ ⌈log₂_⌉ n
  lemma (suc zero) 2≤n = contradiction (s≤s⁻¹ 2≤n) (m+1+n≰m 0)
  lemma (suc (suc zero)) 2≤n = s≤s z≤n
  lemma (suc (suc (suc n))) 2≤n =
    ≤-trans
      (lemma (suc (suc n)) (s≤s (s≤s z≤n)))
      (⌈log₂⌉-mono-≤ (n≤1+n ((suc (suc n)))))
/-}
instance T16 n => QED (T16 n)

instance
  (n < m) => T17 n m
class
  ( n + 1 < m + 1
  ) => T17 n m
{-/ Proof (Agda): T17
open import Data.Nat.Properties using (+-monoˡ-<)
T17 n m cLTb = +-monoˡ-< 1 cLTb
/-}
instance T17 n m => QED (T17 n m)
