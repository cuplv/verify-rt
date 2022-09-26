{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}

module ALang
  ( ALang (ASum, ATimes, FxTerm)
  , NoFx
  , Fun
  , noFx
  , runFun
  , module ALang.Base
  , module Symbol
  ) where

import ALang.Base
import ALang.Internal
import Symbol
