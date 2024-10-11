{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE AllowAmbiguousTypes #-}

module Main where

import GHC.TypeLits (KnownNat, type (+), type (*), Nat, type (<=))

import Data.Proxy (Proxy)
import Data.Constraint (Dict (..))

{- |
 Main entry point.

 `just run` will invoke this function.
-}
main :: IO ()
main = do 
  return ()

-- test :: KnownNat n => Proxy n -> Proxy n
-- test = id

-- test3 :: (KnownNat x) => Proxy x -> Proxy y -> Proxy (x + y) -> Proxy (y + x)
-- test3 _ _ = id

-- test4 :: forall (n :: Nat) . Dict (n <= n + 1)
-- test4 = Dict

type family Dummy (n :: Nat) (m :: Nat) :: Nat where
  Dummy x 3 = (x * x) * x
  Dummy x y = (x * x) * y

test5 :: forall (n :: Nat) (m :: Nat) . (m <= n) => Dict (Dummy n m <= (n * n) * n)
test5 = Dict

test6 :: forall (n :: Nat) (m :: Nat) . (m +1 <= n) => Dict (m <= n)
test6 = Dict
