{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}

module RLang where

import ALang
import Store

data RAlt s a b
  = RAlt { rTerm :: ALang ((s, SState s), a) ((SReq s, SEff s), b) }

data RTerm s a b = RTerm [RAlt s a b]
