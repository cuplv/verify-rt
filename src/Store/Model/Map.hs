module Store.Model.Map where

import Data.Map (Map)
import Data.Set (Set)

data MapView k v
  = MapView { mvNewKeys :: [k]
            , mvValues :: Map k v
            }

data MapReq k
  = MapReq { mrNewKeys :: Int
           , mrValues :: Set k
           }
