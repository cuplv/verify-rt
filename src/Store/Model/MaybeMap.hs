{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}

module Store.Model.MaybeMap where

import ALang
import ALang.Construct
import Symbol
import qualified Symbol.MaybeMap as SMap
import Store.Model

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
  type Rep (Val a b) = SMap.V
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
      return $ ite (isJust a) 
                   (tuple (sJust v1, v2)) 
                   (tuple (sNothing, v2)))
    (\(Val a b) -> (a,b))

data Map a b = Map (Map.Map Int (Val a b))

instance Avs (Map a b) where
  type Rep (Map a b) = SMap.M
  toRep (Map m) | null m = pure SMap.empty
                | otherwise = forall_
  repc = undefined

data Upd a b
  = Insert Key (Val a b)
  | Delete Key
  deriving (Show,Eq,Ord)

instance Avs (Upd a b) where
  type Rep (Upd a b) = SMap.U
  toRep = undefined
  repc = undefined

-- We don't actually want AData, since we have multiple constructors (insert, modify, delete) and we don't care about deconstructing.

-- instance AData (Upd a b) where
