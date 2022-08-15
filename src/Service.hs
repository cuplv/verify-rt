{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}

module Service where

import Symbol

import Data.SBV
import Data.SBV.Either

class Service v where
  svSymbol :: v d a b -> SSpec d a b

data IntSv d a b where
  SvGE :: IntSv Int Int (Either () Int)
  SvAdd :: IntSv Int Int Int

instance Service IntSv where
  svSymbol v = case v of
    SvGE -> SSpec $ \d a -> do
      b <- forall_
      return (d, ite (d .>= b .&& b .>= a) (sRight b) (sLeft su))
    SvAdd -> SSpec $ \d a -> return (d + a, a)
