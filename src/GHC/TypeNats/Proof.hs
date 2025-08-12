{-# LANGUAGE UndecidableSuperClasses #-}
{- | The 'QED' class and a custom dictionary type to be used to
   interface with the plugin.
-}
module GHC.TypeNats.Proof
  ( Rewrite(..)
  , QED(..)
    -- * Supported Operators (re-exported)
  , NonZero
  , type (<)
  , type (<=)
  , type (>)
  , type (>=)
  , type (==)
  , type (<?)
  , type (<=?)
  , type (>?)
  , type (>=?)
  , type (+)
  , type (-)
  , type (*)
  , type (^)
  , type (&&)
  , type (||)
  , Not
  , If
  , Div
  , Mod
  , Min
  , Max
  , Log
  , CLog
  , FLog
  , Log2
  , CLog2
  , FLog2
  , GCD
  , LCM
    -- * Other re-exports
  , Constraint
  )
  where

import Data.Kind (Constraint)
import Data.Type.Bool (type (&&), type (||), Not, If)
import Data.Type.Equality (type (==))
import Data.Type.Ord
  ( type (<), type (<=), type (>), type (>=)
  , type (<?), type (<=?), type (>?), type (>=?)
  )
import GHC.TypeNats (type (+), type (-), type (*), type (^), Div, Mod, Log2)
import GHC.TypeLits.Extra (Min, Max, Log, CLog, FLog, GCD, LCM)

-- | Type alias for 'CLog' with base two.
type CLog2 n = CLog 2 n

-- | Type alias for 'FLog' with base two.
type FLog2 n = FLog 2 n

-- | Type alias for non-zero number constraints.
type NonZero n = 1 <= n

-- | The plugin-specific dictionary type, where we offer our own
-- definition at this point to support availability of the plugin to
-- as many other packages as possible.
--
-- Note that there is currently no default dictionary definition being
-- shipped with base. Hence, you either need to pick one from another
-- package or define it on your own. However, in the former case the
-- utilized package can never utilize the plugin in converse, which is
-- why we stick with the latter solution instead.
data Rewrite (c :: Constraint) = c => Rewrite

-- | A class for sharing evidence of proven statements, which can be
-- easily shared by having a 'QED' instance. The class is also
-- utilized by the automatic proof application feature, which only
-- takes proofs into account that have a corresponding 'QED' instance
-- being in scope.
class c => QED (c :: Constraint) where
  -- | Apply the evidence to eliminate the corresponding constraint.
  apply :: (c => a) -> a
  apply x = x

  -- | Bring the evidence into scope via a t'Rewrite' dictionary.
  using :: Rewrite c
  using = Rewrite
