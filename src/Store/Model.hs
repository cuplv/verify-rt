{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeFamilies #-}

module Store.Model where

import ALang
import Symbol

class (Avs u, Avs (UState u)) => Update u where
  type UState u
  idU :: u
  seqU :: ALang' (u,u) u
  applyU :: ALang' (u, UState u) (UState u)

class (Avs k, Update (KUpd k)) => Capability k where
  type KUpd k

class (Avs c, Capability (CCap c)) => Context c where
  type CCap c
  capC :: ALang' (c, KUpd (CCap c)) Bool
  envC :: ALang' (c, State c, KUpd (CCap c)) Bool

class (Avs r, Context (Ctx r)) => Request r where
  type Ctx r

type Cap r = CCap (Ctx r)

type Upd r = KUpd (Cap r)

type State r = UState (Upd r)
