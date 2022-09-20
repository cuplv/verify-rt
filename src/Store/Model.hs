{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeFamilies #-}

module Store.Model where

import Symbol

class Update u where
  type UState u
  idU :: u
  seqU :: u -> u -> u
  applyU :: u -> UState u -> UState u

class Context c where
  type CUpd c
  capPermits :: c -> CUpd c -> Bool
  envPermits :: c -> CUpd c -> Bool

class (Context (Ctx r)) => RequestL r where
  type Ctx r

type Upd r = CUpd (Ctx r)

type State r = UState (Upd r)
