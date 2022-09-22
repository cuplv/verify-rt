{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}

module RLang where

import ALang
import Store.Model

data Transact r w b
  = Transact { trReq :: Fun w r
             , trBody :: Fun (Ctx r, w) (Upd r, b)
             }
