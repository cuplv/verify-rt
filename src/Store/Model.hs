{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

module Store.Model where

import ALang
import ALang.Base (AData (..))
import ALang.Construct

import Data.SBV
import Data.SBV.Tuple

class (Avs u, Avs (UState u)) => Update u where
  type UState u
  idU :: u
  seqU :: u -> Fun (u,u) u
  applyU :: u -> Fun (u, UState u) (UState u)
  symU :: u -> Sy u -> Sy (UState u) -> Symbolic (Sy (UState u))
  symU z u s = symbolize (applyU z) (tuple (u,s))

instance Update () where
  type UState () = ()
  idU = ()
  seqU _ = ca ()
  applyU _ = ca ()

data NoUpd s = NoUpd deriving (Show,Eq,Ord)

instance Avs (NoUpd s) where
  type Rep (NoUpd s) = ()
  toRep _ = return su
  repc _ _ = sTrue

instance (Avs s) => Update (NoUpd s) where
  type UState (NoUpd s) = s
  idU = NoUpd
  seqU _ = ca NoUpd
  applyU _ = tup2g2

class (Avs g, Avs (GState g), Update (GUpd g)) => Grant g where
  type GUpd g
  readG :: g -> Sy g -> Sy (GState g) -> Sy (GState g) -> Symbolic SBool
  writeG :: g -> Sy g -> Sy (GState g) -> Sy (GState g) -> Symbolic SBool
  useG :: g -> Fun (GUpd g, g) (Maybe g)

type GState g = UState (GUpd g)

data Context g
  = Context { ctxState :: GState g
            , ctxGrant :: g
            }

instance (Grant g) => Avs (Context g) where
  type Rep (Context g) = (Rep (GState g), Rep g)
  toRep (Context s g) = fmap tuple $
    (,) <$> toRep s <*> toRep g
  repc (Context s g) = repc (s,g)

instance (Grant g) => AData (Context g) where
  type Content (Context g) = (GState g, g)
  conA = ArrF return (\(a,b) -> Context a b)
  deconA = ArrF return (\(Context a b) -> (a,b))

getState :: (Grant g) => ALang t (Context g) (GState g)
getState = deconA >>> tup2g1

stateE :: (Avs a, Grant g) => ALang t a (Context g) -> ALang t a (GState g)
stateE m = m >>> getState

stateS :: (SymVal s, SymVal g) => SBV (s,g) -> SBV s
stateS = _1

getGrant :: (Grant g) => ALang t (Context g) g
getGrant = deconA >>> tup2g2

grantE :: (Avs a, Grant g) => ALang t a (Context g) -> ALang t a g
grantE m = m >>> getGrant


grantS :: (SymVal s, SymVal g) => SBV (s,g) -> SBV g
grantS = _2

readCtx :: (Grant g) => g -> Sy (Context g) -> Sy (GState g) -> Symbolic SBool
readCtx z ctx = readG z (grantS ctx) (stateS ctx)
