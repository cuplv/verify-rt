module Store.Model.Int where

data IntView
  = IntView { ivLow :: Maybe Int
            , ivHigh :: Maybe Int
            , ivAdd :: Maybe Int
            , ivSub :: Maybe Int
            }
