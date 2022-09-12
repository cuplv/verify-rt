{-# LANGUAGE TypeFamilies #-}

module Store where

class StoreView s where
  type SReq s
  type SCap s
  type SEff s
  type SState s
