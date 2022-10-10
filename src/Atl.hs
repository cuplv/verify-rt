{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

module Atl where

import ALang
import ALang.Construct
import Store.Model
import Symbol
import Verify

import Data.SBV
import Data.SBV.Either
import Data.SBV.Maybe
import Data.SBV.Set
import Data.SBV.Tuple
import qualified Data.SBV.List as SList

class (Avs r, Grant (Gr r)) => Request r where
  type Gr r
  emptyReq :: r
  reqPred :: r -> Sy r -> Sy (Ctx r) -> Symbolic SBool
  seqR :: r -> r -> r
  seqCR :: r -> Sy r -> Binr (Sy (Ctx r))
  reqAddCap :: r -> Sy r -> Binr (Sy (Gr r))
  reqEnv :: r -> Sy r -> Sy (Ctx r) -> Symbolic SBool
  minReq :: Fun (Upd r) r

type State r = GState (Gr r)

type Upd r = GUpd (Gr r)

type Ctx r = Context (Gr r)

-- reqMake :: (Request r, Avs w) => r -> ReqMake w r
-- reqMake r = ReqMake { rmReq = const r
--                     , rmPred = sndA (reqPred r) >>> get2
--                     }

-- data ReqMake w r
--   = ReqMake { rmReq :: w -> r
--             , rmPred :: Fun (w, Ctx r) Bool
--             }

-- rmExtend 
--   :: (Avs w1, Avs w2, Request r)
--   => Fun w1 w2
--   -> ReqMake w2 r
--   -> ReqMake w1 r
-- rmExtend f (ReqMake r p) = ReqMake (r . runFun f) (over1 f >>> p)


data Action r w a b where
  SlConfig :: Action r w a w
  SlReConfig :: (Avs w2) => Fun w1 w2 -> Atl r w2 a b -> Action r w1 a b
  SlContext :: Action r w a (Ctx r)
  SlRequest :: Action r r a a
  SlUpdate :: Action r w (Upd r) ()
  SlCancel :: Action r w a b

type Atl r w = ALang (Action r w)

cancel :: (Request r, Avs w, Avs a, Avs b) => Atl r w a b
cancel = FxTerm SlCancel

-- request
--   :: (Request r, Avs w, Avs a)
--   => ReqMake w r
--   -> Atl r w a (Ctx r)
-- request r = FxTerm (SlRequest r) >>> FxTerm SlContext

reConf
  :: (Avs a, Avs b, Avs w1, Avs w2)
  => Fun w1 w2
  -> Atl r w2 a b
  -> Atl r w1 a b
reConf f = FxTerm . SlReConfig f

request
  :: (Request r, Avs a, Avs w)
  => Fun w r
  -> Atl r w a a
request f = reConf f (FxTerm SlRequest)

-- Use minReq to make the minimal Request that will cover this
-- statically determined effect.
updateS
  :: (Request r, Avs w, Avs a)
  => Fun w (Upd r)
  -> Atl r w a a
updateS f = passThru $
  reConf f (request minReq >>> getConf >>> FxTerm SlUpdate)
-- updateS f = FxTerm (SlReConfig (f >>> minReq)) >>> getConf >>> noFx f
-- updateS f =
--   FxTerm (SlRequest (rmExtend f minReq))
--   >>> getConf
--   >>> noFx f
--   >>> FxTerm SlUpdate

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

splitP
  :: (SymVal a, SymVal b, SymVal c)
  => String
  -> (SBV a, SBV c)
  -> Symbolic ((SBV a, SBV b), (SBV b, SBV c))
splitP s (a,c) = do
  b <- forall s
  return ((a,b), (b,c))

-- symAtl
--   :: (Request r, Avs w, Avs a, Avs b)
--   => (r, Gr r, Upd r) -- witness values for Request, Grant, and Effect types
--   -> Atl r w a b
--   -> Sy w
--   -> (Sy a, Sy b)
--   -> (Sy (Ctx r), Sy (Ctx r))
--   -> (Sy (State r), Sy (State r))
--   -> Symbolic SBool
-- symAtl (zr,zg,zu) m w val ctx state = case m of
--   ASequenceLR ml mr -> do
--     (val1,val2) <- splitP "valStep" val
--     (ctx1,ctx2) <- splitP "ctxStep" ctx
--     (state1,state2) <- splitP "stateStep" state
--     constrain =<< symAtl (zr,zg,zu) ml w val1 ctx1 state1
--     symAtl (zr,zg,zu) mr w val2 ctx2 state2
--   ArrF sf ff -> pureF $ ArrF sf ff
--   ArrP sp ff -> pureF $ ArrP sp ff

--   FxTerm fx -> case fx of
--     SlConfig -> return (eFree .&& snd val .== w)
--     SlReConfig f m1 -> do
--       w1 <- forall "reconfig"
--       constrain =<< symbolize f w w1
--       symAtl (zr,zg,zu) m1 w1 val ctx state
--     SlContext -> return (eFree .&& snd val .== snd ctx)
--     SlRequest -> do
--       -- The request witness (zr) is used here
--       p1 <- reqAddCap zr w (grantS (fst ctx)) (grantS (snd ctx))
--       p2 <- reqEnv zr w (fst ctx)
--       return (p1 .&& p2 .&& fst val .== snd val .&& fst state .== snd state)
--     SlUpdate -> do
--       p1 <- symU zu (fst val) (stateS (fst ctx)) (stateS (snd ctx))
--       p2 <- symU zu (fst val) (fst state) (snd state)
--       p3 <- symbolize 
--               (useG zg) 
--               (tuple (fst val, grantS (fst ctx))) 
--               (sJust $ grantS (snd ctx))
--       return (p1 .&& p2 .&& p3)
--     SlCancel -> return sFalse

--   where eFree =
--           fst state .== snd state
--           .&& fst ctx .== snd ctx
--         pureF f = (eFree .&&) <$> symbolize f (fst val) (snd val)
