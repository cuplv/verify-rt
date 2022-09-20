{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}

module ALang.Example where

import ALang
import Data.Map (Map)
import Data.SBV
import qualified Data.SBV.List as SList
import Store.Model

{-| Subtract the input amount from the state, if the amount is
  available. -}
takeStock :: SLang Int IntView () (Either String Int)
takeStock =
  -- Check that the state's value is greater than or equal to the
  -- transaction's input value.
   query (VdTerm MkAtLeast)
     -- If so, subtract the input value.  Then, return the input value.
     (effectSub >>> getConf)
     -- If not, return an explanation of failure.
     (Const "Not enough stock.")

effectSub :: (Avs a) => SLang Int IntView a ()
effectSub =
  assert (VdTerm MkSubCap)
  >>| getConf
  >>> VdTerm Negate
  >>> update

data IntVVd a b where
  MkSubCap :: IntVVd Int IntReq
  MkAtLeast :: IntVVd Int IntReq

instance ValDomain IntVVd where
  vdSymbol = undefined
