module Verify where

import ALang
import Store.Model
import Symbol

import Data.SBV
import qualified Data.SBV.Maybe as SM
import Data.SBV.Tuple

type Transact' k w b = Fun (Context k, w) (Maybe (KUpd k, b))

symT
  :: (Capability k, Avs w, Avs b)
  => Transact' k w b
  -> (Sy (UState (KUpd k)), Sy k, Sy k)
  -> Sy w
  -> Symbolic (Sy (Maybe (KUpd k, b)))
symT f (s,e,c) w = do
  symbolize f $ tuple (tuple (s,e,c), w)

data PrePost k w b
  = PrePost { ppPre :: Sy (UState (KUpd k)) -> Sy w -> Symbolic SBool
            , ppPost :: Sy (UState (KUpd k)) -> Sy b -> Symbolic SBool
            } 

stateSpec
  :: (Capability k, Avs w, Avs b)
  => (k, KUpd k)
  -> Transact' k w b
  -> PrePost k w b
  -> Symbolic SBool
stateSpec (y,z) f (PrePost p q) = do
  w <- forall "w"
  s <- forall "state"
  env <- forall "env"
  cap <- forall "cap"

  r <- symT f (s,env,cap) w

  ue <- exists "ue"
  ueC <- symbolize (permitC y) (tuple (ue,env))
  s1 <- symbolize (applyU z) (tuple (ue,s))

  pTrue <- p s1 w

  let u = _1 (SM.fromJust r)
      b = _2 (SM.fromJust r)

  ua <- forall "ua"
  uaC <- symbolize (permitC y) (tuple (ua,env))
  u' <- symbolize (seqU z) (tuple (ua,u))
  s2 <- symbolize (applyU z) (tuple (u',s))

  qt' <- q s2 b
  let qTrue = SM.maybe sTrue (const qt') r

  return $ sNot (constrainC y env .&& constrainC y cap)
           .|| (ueC .&& sNot pTrue)
           .|| (uaC .=> qTrue)

capSpec
  :: (Capability k, Avs w, Avs b)
  => (k, KUpd k)
  -> Transact' k w b
  -> Symbolic SBool
capSpec (y,z) f = do
  w <- forall "w"
  s <- forall "state"
  env <- forall "env"
  cap <- forall "cap"

  r <- symT f (s,env,cap) w

  let u = _1 (SM.fromJust r)
      b = _2 (SM.fromJust r)

  p <- symbolize (permitC y) (tuple (u,cap))
  return $ sNot (constrainC y env .&& constrainC y cap)
           .|| SM.isNothing r
           .|| p

safeTr
  :: (Capability k, Avs w, Avs b)
  => (k, KUpd k)
  -> Transact' k w b
  -> PrePost k w b
  -> Symbolic SBool
safeTr x f p = do
  r1 <- stateSpec x f p
  r2 <- capSpec x f
  return (r1 .&& r2) 
