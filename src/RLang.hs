{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}

module RLang where

import Store.Model

data RAlt r w b
  = RAlt { rReq :: w -> r
         , rBody :: (Context (Cap r), w) -> (Upd r, b)
         }

data RLang r w b = RLang [RAlt r w b]
