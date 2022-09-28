module Verify where

import ALang
import Store.Model
import Symbol

import Data.SBV
import Data.SBV.Tuple

type Transact' k w b = Fun (Context k, w) (KUpd k, b)

symT
  :: (Capability k, Avs w, Avs b)
  => Transact' k w b
  -> (Sy (UState (KUpd k)), Sy k, Sy k)
  -> Sy w
  -> Symbolic (Sy (KUpd k), Sy b)
symT f (s,e,c) w = do
  r <- symbolize f $ tuple (tuple (s,e,c), w)
  return (_1 r, _2 r)

data PrePost k w b
  = PrePost { ppPre :: Sy (UState (KUpd k)) -> Sy w -> Symbolic SBool
            , ppPost :: Sy (UState (KUpd k)) -> Sy b -> Symbolic SBool
            } 

repSpec
  :: (Capability k, Avs w, Avs b)
  => (k, KUpd k)
  -> Transact' k w b
  -> PrePost k w b
  -> Symbolic SBool
repSpec (y,z) f (PrePost p q) = do
  w <- forall_
  s <- forall_
  env <- forall_
  cap <- forall_

  (u,b) <- symT f (s,env,cap) w

  ue <- exists_
  ueC <- symbolize (permitC y) (tuple (ue,env))
  constrain ueC
  s1 <- symbolize (applyU z) (tuple (ue,s))

  ua <- forall_
  uaC <- symbolize (permitC y) (tuple (ua,env))
  constrain uaC
  u' <- symbolize (seqU z) (tuple (ua,u))
  s2 <- symbolize (applyU z) (tuple (u',s))

  pTrue <- p s1 w
  qTrue <- q s2 b

  return (sNot pTrue .|| qTrue)
