{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

module Store.Model where

import ALang

class (Avs u, Avs (UState u)) => Update u where
  type UState u
  idU :: u
  seqU :: Fun (u,u) u
  applyU :: Fun (u, UState u) (UState u)

class (Avs k, Update (KUpd k)) => Capability k where
  type KUpd k

class (Avs r, Capability (Cap r)) => Request r where
  type Cap r
  seqR :: Fun (r,r) r
  minReq :: Fun (Upd r) r

type Upd r = KUpd (Cap r)

type State r = UState (Upd r)

data Context k
  = Context { ctxState :: UState (KUpd k)
            , ctxEnv :: k
            , ctxCap :: k
            }

type Ctx r = Context (Cap r)

instance (Capability k) => Avs (Context k) where
  type Rep (Context k) = (Rep (UState (KUpd k)), Rep k, Rep k)
  toRep (Context s e c) = (toRep s, toRep e, toRep c)
