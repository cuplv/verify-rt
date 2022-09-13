{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}

module RLang where

import ALang
import Store

data RAlt s a b
  = RAlt { rReq :: a -> SReq s
         , rBody :: (s, a) -> (SEff s, b)
         }

data RTerm s a b = RTerm [RAlt s a b]
