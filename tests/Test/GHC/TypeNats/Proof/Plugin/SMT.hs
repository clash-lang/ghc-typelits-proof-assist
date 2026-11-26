{-# LANGUAGE Safe #-}
{-# LANGUAGE NoGeneralizedNewtypeDeriving #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}

module Test.GHC.TypeNats.Proof.Plugin.SMT where

import GHC.TypeNats.Proof

{-/ Preamble (SMT):
(set-logic QF_NIA)
/-}

instance T0 n
class
  ( 2 * n ~ n + n
  ) => T0 n
{-/ Proof (SMT): T0
/-}
instance T0 n => QED (T0 n)

instance T1 n
class
  ( 2 * n - n ~ n
  ) => T1 n
{-/ Proof (SMT): T1
/-}
instance T1 n => QED (T1 n)

instance T2 n
class
  ( n `Div` 2 <= n
  ) => T2 n
{-/ Proof (SMT): T2
/-}
instance T2 n => QED (T2 n)

instance T3 n
class
  ( n `Mod` 2 < 2
  ) => T3 n
{-/ Proof (SMT): T3
/-}
instance T3 n => QED (T3 n)

instance
  ( m >= n
  ) => T4 m n
class
  ( Max m n ~ m
  ) => T4 m n
{-/ Proof (SMT): T4
/-}
instance T4 m n => QED (T4 m n)

instance
  ( m <= n
  ) => T5 m n
class
  ( Min m n ~ m
  ) => T5 m n
{-/ Proof (SMT): T5
/-}
instance T5 m n => QED (T5 m n)

instance
  ( 1 <= n
  , 1 <= d
  ) => T6 n d
class
  ( 1 <= (n + (d - 1)) `Div` d
  ) => T6 n d
{-/ Proof (SMT): T6
/-}
instance T6 n d => QED (T6 n d)