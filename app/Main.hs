module Main where

import GHC.TypeLits (KnownNat, type (+), type (*))

import Data.Proxy (Proxy)

{- |
 Main entry point.

 `just run` will invoke this function.
-}
main :: IO ()
main = do 
  return ()

test :: KnownNat n => Proxy n -> Proxy n
test = id

test3 :: (KnownNat x) => Proxy x -> Proxy y -> Proxy (x + y) -> Proxy (y + x)
test3 _ _ = id

