{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

module Atl where

import ALang
import RLang
import Store.Model
import Symbol

import Data.SBV
import Data.SBV.Either
import Data.SBV.Set
import Data.SBV.Tuple
import qualified Data.SBV.List as SList

data Action r w a b where
  SlConfig :: Action r w () w
  SlReConfig :: ALang' w1 w2 -> Atl r w2 a b -> Action r w1 a b
  SlContext :: Action r w () (Ctx r)
  SlRequest :: ALang' w r -> Action r w () ()
  SlAlt :: Atl r w () b1 -> Atl r w () b2 -> Action r w () (Either b1 b2)
  SlUpdate :: Action r w (Upd r) ()

type Atl r w = ALang (Action r w)

instance (Request r, Avs w) => Fx (Action r w) where
  type FxRep (Action r w) = (State r, Cap r, Cap r)
  fxSym = undefined

query
  :: (Request r, Avs w, Avs a, Avs b1, Avs b2)
  => ALang' w r
  -> Atl r w () b1
  -> Atl r w (Ctx r) b2
  -> Atl r w a (Either b1 b2)
query r a1 a2 = Forget >>> FxTerm
  (SlAlt a1 (FxTerm (SlRequest r) >>> FxTerm SlContext >>> a2))

-- Use minReq to make the minimal Request that will cover this
-- statically determined effect.
updateS
  :: (Request r, Avs w, Avs a)
  => ALang' w (Upd r)
  -> Atl r w a ()
updateS f =
  Forget
  >>> FxTerm (SlRequest (f >>> minReq))
  >>> FxTerm SlConfig
  >>> liftNoFx f
  >>> FxTerm SlUpdate

getConf
  :: (Request r, Avs w, Avs a)
  => Atl r w a w
getConf = Forget >>> FxTerm SlConfig

-- compile :: (StoreView s) => SLang w s a b -> RLang w s b
-- compile t = case t of
--   SlConf -> RLang [RAlt (const emptyR) (\(w,_) -> (idE, w))]
--   SlService (Service f) -> RLang
--     [RAlt (interpret f) (\(_,s) -> (idE, Right s))
--     ,RAlt (const emptyR) (const (idE, Left ()))
--     ]

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
