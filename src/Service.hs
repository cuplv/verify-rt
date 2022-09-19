{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

module Service where

import ALang
import RLang
import Store
import Symbol

import Data.Map (Map)
import Data.SBV
import Data.SBV.Either
import Data.SBV.Set
import Data.SBV.Tuple
import qualified Data.SBV.List as SList

data Action w s a b where
  SlConf :: Action w s () w
  SlQuery
    :: ALang' w (SReq s)
    -> SLang w s s b1
    -> SLang w s () b2
    -> Action w s () (Either b2 b1)
  SlAssert :: ALang' w (SReq s) -> Action w s () s
  SlUpdate :: Action w s (SEff s) ()

type SLang w s = ALang (Action w s) 

query
  :: (Avs w, Avs (SEff s), Avs (SState s), Avs (SCap s), Avs a, Avs b1, Avs b2)
  => ALang' w (SReq s)
  -> SLang w s s b1
  -> SLang w s () b2
  -> SLang w s a (Either b2 b1)
query r a1 a2 = Forget >>> FxTerm (SlQuery r a1 a2)

assert
  :: (Avs s, Avs w, Avs (SEff s), Avs (SState s), Avs (SCap s), Avs a)
  => ALang' w (SReq s)
  -> SLang w s a s
assert r = Forget >>> FxTerm (SlAssert r)

getConf
  :: (Avs w, Avs (SEff s), Avs (SState s), Avs (SCap s), Avs a)
  => SLang w s a w
getConf = Forget >>> FxTerm SlConf

update
  :: (Avs w, Avs (SEff s), Avs (SState s), Avs (SCap s))
  => SLang w s (SEff s) ()
update = FxTerm SlUpdate

instance (Avs w, Avs (SEff s), Avs (SState s), Avs (SCap s)) => Fx (Action w s) where
  type FxRep (Action w s) = (SState s, SCap s, SCap s, SEff s)
  fxSym = undefined

-- compile :: (StoreView s) => SLang w s a b -> RLang w s b
-- compile t = case t of
--   SlConf -> RLang [RAlt (const emptyR) (\(w,_) -> (idE, w))]
--   SlService (Service f) -> RLang
--     [RAlt (interpret f) (\(_,s) -> (idE, Right s))
--     ,RAlt (const emptyR) (const (idE, Left ()))
--     ]
