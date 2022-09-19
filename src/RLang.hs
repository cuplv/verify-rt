{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}

module RLang where

import ALang
import Store

data RAlt w s b
  = RAlt { rReq :: w -> SReq s
         , rBody :: (w, s) -> (SEff s, b)
         }

data RLang w s b = RLang [RAlt w s b]
