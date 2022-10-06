{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

module Atl where

import ALang
import Store.Model
import Symbol

import Data.SBV
import Data.SBV.Either
import Data.SBV.Set
import Data.SBV.Tuple
import qualified Data.SBV.List as SList

class (Grant (Gr r), Update (Upd r)) => Request r where
  type Upd r
  type Gr r
  emptyReq :: r
  reqPred :: r -> Fun (Ctx r) Bool
  seqR :: r -> r -> r
  minReq :: ReqMake (Upd r) r

type State r = UState (Upd r)

type Ctx r = Context (Gr r)

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


data Action r w a b where
  SlConfig :: Action r w a w
  SlReConfig :: Fun w1 w2 -> Atl r w2 a b -> Action r w1 a b
  SlContext :: Action r w a (Ctx r)
  SlRequest :: ReqMake w r -> Action r w a ()
  SlUpdate :: Action r w (Upd r) ()
  SlCancel :: Action r w a b

type Atl r w = ALang (Action r w)

cancel :: (Request r, Avs w, Avs a, Avs b) => Atl r w a b
cancel = FxTerm SlCancel

request
  :: (Request r, Avs w, Avs a)
  => ReqMake w r
  -> Atl r w a (Ctx r)
request r = FxTerm (SlRequest r) >>> FxTerm SlContext

-- Use minReq to make the minimal Request that will cover this
-- statically determined effect.
updateS
  :: (Request r, Avs w, Avs a)
  => Fun w (Upd r)
  -> Atl r w a ()
updateS f =
  FxTerm (SlRequest (rmExtend f minReq))
  >>> getConf
  >>> noFx f
  >>> FxTerm SlUpdate

getConf
  :: (Request r, Avs w, Avs a)
  => Atl r w a w
getConf = FxTerm SlConfig

type AtlModel s c u w a b 
  = (s,c,c) -> w -> a -> Symbolic (u, b)

data AtlSpec r w a b
  = AtlSpec { sPre :: Sy (State r) -> Sy w -> Sy a -> Symbolic SBool
            , sPost :: Sy (State r) -> Sy b -> Symbolic SBool
            }

prePost
  :: (Request r, Avs w, Avs a, Avs b)
  => (Sy (State r) -> SBool)
  -> (Sy (State r) -> SBool)
  -> AtlSpec r w a b
prePost p q = AtlSpec
  (\s _ _ -> return $ p s)
  (\s _ -> return $ q s)
