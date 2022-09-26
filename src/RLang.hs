{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}

module RLang where

import ALang
import Store.Model

data Transact r w b
  = Transact { trReq :: w -> r
             , trBody :: Fun (Ctx r, w) (Upd r, b)
             }
