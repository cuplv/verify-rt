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
  SlConf :: Action r w () w
  SlQuery
    :: ALang' w r
    -> Atl r w (Ctx r) b1
    -> Atl r w () b2
    -> Action r w () (Either b2 b1)
  SlAssert :: ALang' w r -> Action r w () s
  SlUpdate :: Action r w (Upd r) ()

type Atl r w = ALang (Action r w) 

query
  :: (Request r, Avs w, Avs a, Avs b1, Avs b2)
  => ALang' w r
  -> Atl r w (Ctx r) b1
  -> Atl r w () b2
  -> Atl r w a (Either b2 b1)
query r a1 a2 = Forget >>> FxTerm (SlQuery r a1 a2)

assert
  :: (Request r, Avs w, Avs a)
  => ALang' w r
  -> Atl r w a (Ctx r)
assert r = Forget >>> FxTerm (SlAssert r)

getConf
  :: (Request r, Avs w, Avs a)
  => Atl r w a w
getConf = Forget >>> FxTerm SlConf

update
  :: (Request r, Avs w)
  => Atl r w (Upd r) ()
update = FxTerm SlUpdate

instance (Request r, Avs w) => Fx (Action r w) where
  type FxRep (Action r w) = (State r, Cap r, Cap r, Upd r)
  fxSym = undefined

-- compile :: (StoreView s) => SLang w s a b -> RLang w s b
-- compile t = case t of
--   SlConf -> RLang [RAlt (const emptyR) (\(w,_) -> (idE, w))]
--   SlService (Service f) -> RLang
--     [RAlt (interpret f) (\(_,s) -> (idE, Right s))
--     ,RAlt (const emptyR) (const (idE, Left ()))
--     ]
