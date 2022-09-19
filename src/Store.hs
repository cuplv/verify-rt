{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeFamilies #-}

module Store where

import Data.Map (Map)
import Data.Set (Set)
import Symbol

class Request r where
  emptyR :: r

class Effect e where
  idE :: e

instance Effect Int where
  idE = 0

instance Request IntReq where
  emptyR = IntReq Nothing Nothing (Just 0) (Just 0)

instance Avs IntReq where
  type Rep IntReq = ()

instance Avs IntView where
  type Rep IntView = ()

class (Effect (SEff s), Request (SReq s)) => StoreView s where
  type SReq s
  type SCap s
  type SEff s
  type SState s

data IntReq
  = IntReq { irLow :: Maybe Int
           , irHigh :: Maybe Int
           , irAdd :: Maybe Int
           , irSub :: Maybe Int
           }

data IntView
  = IntView { ivLow :: Maybe Int
            , ivHigh :: Maybe Int
            , ivAdd :: Maybe Int
            , ivSub :: Maybe Int
            }

data MapReq k
  = MapReq { mrNewKeys :: Int
           , mrValues :: Set k
           }

data MapView k v
  = MapView { mvNewKeys :: [k]
            , mvValues :: Map k v
            }

instance StoreView (IntView) where
  type SReq IntView = IntReq
  type SCap IntView = ()
  type SEff IntView = Int
  type SState IntView = Int
