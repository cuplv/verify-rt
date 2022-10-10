{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}

module ALang
  ( ALang
  , NoFx
  , Fun
  , noFx
  , runFun
  , symbolize
  , module ALang.Base
  , module Symbol
  ) where

import ALang.Base
import ALang.Internal
import Symbol
