{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

module Service where

import Symbol

import Data.Map (Map)
import Data.SBV
import Data.SBV.Either
import Data.SBV.Set
import Data.SBV.Tuple
import qualified Data.SBV.List as SList

{-| 'Service' terms interact with the state, querying consistent
  information about it and modifying it.

  A 'Service' term has three argument types: @d@ is the state type,
  @a@ is the term's input type, and @b@ is the output type.
-}
class (Avs (SvState v)) => Service v where
  type SvState v

  {-| Get the symbolic specification of the term's behavior, including its
    interaction with the state and its output value, with respect to its
    input value. -}
  svSymbol :: v a b -> SSpec (SvState v) a b

{-| A 'Service' for an integer counter state. -}
data IntSv a b where
  {-| Check whether the state value is greater-than or equal-to the input
  value.  If so, return @Right n@, where @n@ is a stable lower-bound
  on the state's value.  Else, return @Left ()@. -}
  SvGE :: IntSv Int (Either () Int)

  {-| Add the input value to the store.  This can also be used to
  subtract, by passing a negative input value. -}
  SvAdd :: IntSv Int ()

instance Service IntSv where
  type SvState IntSv = Int

  svSymbol v = case v of

    SvGE -> SSpec $ \d a -> do
      b <- forall_
      return (d, ite (d .>= b .&& b .>= a) (sRight b) (sLeft su))

    SvAdd -> SSpec $ \d a -> return (d + a, su)

data MapSv k w a b where
  SvFreshKey :: MapSv k w () k
  SvInsert :: MapSv k w (k,w) ()

instance (Ord (Rep k), Avs k, Avs w) => Service (MapSv k w) where
  type SvState (MapSv k w) = Map k w

  svSymbol v = case v of
    SvFreshKey -> SSpec $ \d a -> do
      k <- forall "freshKey"
      constrain $ SList.notElem k d
      return (d, k)
    SvInsert -> SSpec $ \d a -> do
      return (_1 a SList..: d, su) 
