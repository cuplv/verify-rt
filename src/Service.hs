{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

module Service where

import ALang
import Store
import Symbol

import Data.Map (Map)
import Data.SBV
import Data.SBV.Either
import Data.SBV.Set
import Data.SBV.Tuple
import qualified Data.SBV.List as SList

data Service s a
  = Service (ALang a (SReq s, SEff s))

data ReadService s a
  = ReadService { rsReq :: ALang (Ab a) (SReq s) }

data WriteService s a
  = WriteService (ALang a (SEff s))

data SLang s a b where
  SlPure :: ALang a b -> SLang s a b
  SlService :: Service s a -> SLang s a (Either () s)
