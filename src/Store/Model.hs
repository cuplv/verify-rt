{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

module Store.Model where

import ALang
import ALang.Base (AData (..))
import ALang.Construct

class (Avs u, Avs (UState u)) => Update u where
  type UState u
  idU :: u
  seqU :: Fun (u,u) u
  applyU :: Fun (u, UState u) (UState u)

class (Avs k, Update (KUpd k)) => Capability k where
  type KUpd k
  permitC :: Fun (KUpd k, k) Bool

class (Capability (Cap r)) => Request r where
  type Cap r
  emptyReq :: r
  reqPred :: r -> Fun (Ctx r) Bool
  seqR :: r -> r -> r
  minReq :: ReqMake (Upd r) r

reqMake :: (Request r, Avs w) => r -> ReqMake w r
reqMake r = ReqMake { rmReq = const r
                    , rmPred = sndA (reqPred r) >>> get2
                    }

data ReqMake w r
  = ReqMake { rmReq :: w -> r
            , rmPred :: Fun (w, Ctx r) Bool
            }

rmExtend 
  :: (Avs w1, Avs w2, Request r)
  => Fun w1 w2
  -> ReqMake w2 r
  -> ReqMake w1 r
rmExtend f (ReqMake r p) = ReqMake (r . runFun f) (over1 f >>> p)

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

instance (Capability k) => AData (Context k) where
  type Content (Context k) = (UState (KUpd k), k, k)
  conA = Arr return (\(a,b,c) -> Context a b c)
  deconA = Arr return (\(Context a b c) -> (a,b,c))

getState :: (Capability k) => ALang t (Context k) (UState (KUpd k))
getState = deconA >>> tup3g1

getEnv :: (Capability k) => ALang t (Context k) k
getEnv = deconA >>> tup3g2

getCap :: (Capability k) => ALang t (Context k) k
getCap = deconA >>> tup3g3
