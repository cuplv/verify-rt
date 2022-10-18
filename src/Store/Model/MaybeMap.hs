{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}

module Store.Model.MaybeMap where

import ALang
import ALang.Construct
import Symbol
import qualified Symbol.MaybeMap as SMap
import Store.Model

import Data.Map (Map)
import qualified Data.Map as Map
import Data.SBV
import Data.SBV.Maybe
import Data.SBV.Tuple

type Key = Int

data Val a b
  = Val { valMain :: Maybe a
        , valAux :: b
        }
  deriving (Show,Eq,Ord)

instance Avs (Val a b) where
  type Rep (Val a b) = Maybe SMap.MaybeMapVal
  toRep (Val (Just _) _) = sJust <$> forall_
  toRep _ = pure sNothing
  repc (Val (Just _) _) = isJust
  repc _ = isNothing

instance (Avs a, Avs b) => AData (Val a b) where
  type Content (Val a b) = (Maybe a, b)
  conA = ArrF
    (\a -> do
      v <- forall_
      return $ ite (isJust (_1 a))
                   (sJust v)
                   sNothing)
    (\(a,b) -> Val a b)
  deconA = ArrF
    (\a -> do
      v1 <- forall_
      v2 <- forall_
      return $ ite (isJust a) (tuple (sJust v1, v2)) (tuple (sNothing, v2)))
    (\(Val a b) -> (a,b))
