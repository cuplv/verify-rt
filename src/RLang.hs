{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}

module RLang where

import Store.Model

data RAlt r c w b
  = RAlt { rReq :: w -> r
         , rBody :: (c, w) -> (CUpd c, b)
         }

data RLang r c w b = RLang [RAlt r c w b]
