{-# LANGUAGE TypeFamilies #-}

module Store where

import Data.Map (Map)
import Data.Set (Set)

class StoreView s where
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
