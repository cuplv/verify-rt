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

seqE :: (Avs a, Update u) => u -> Fun a u -> Fun a u -> Fun a u
seqE uw m1 m2 = (m1 &&& m2) >>> seqU uw

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

instance (Update a, Update b) => Update (a,b) where
  type UState (a,b) = (UState a, UState b)
  idU = (idU,idU)
  seqU (aw,bw) =
    tup2 $ \u1 u2 -> 
    tup2' u1 $ \a1 b1 ->
    tup2' u2 $ \a2 b2 ->
    seqE aw a1 a2 &&& seqE bw b1 b2
  applyU (aw,bw) =
    tup22 idA $ \((ua,ub), (sa,sb)) ->
    eform2 (applyU aw) ua sa
    &&& eform2 (applyU bw) ub sb

class (Avs g, Avs (GState g), Update (GUpd g)) => Grant g where
  type GUpd g
  readG :: g -> Sy g -> Sy (GState g) -> Sy (GState g) -> Symbolic SBool
  writeG :: g -> Sy g -> Sy (GState g) -> Sy (GState g) -> Symbolic SBool
  useG :: g -> Fun (GUpd g, g) (Maybe g)

type GState g = UState (GUpd g)

instance (Grant a, Grant b) => Grant (a,b) where
  type GUpd (a,b) = (GUpd a, GUpd b)
  readG (aw,bw) g s1 s2 = do
    a <- readG aw (_1 g) (_1 s1) (_1 s2) 
    b <- readG bw (_2 g) (_2 s1) (_2 s2) 
    return (a .&& b)
  writeG (aw,bw) g s1 s2 = do
    a <- writeG aw (_1 g) (_1 s1) (_1 s2) 
    b <- writeG bw (_2 g) (_2 s1) (_2 s2) 
    return (a .&& b)
  useG (wa,wb) =
    tup22 idA $ \((ua,ub), (sa,sb)) ->
    eform2 
      bothA 
      (eform2 (useG wa) ua sa) 
      (eform2 (useG wb) ub sb)

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

tup2Ctx 
  :: (Avs a, Grant g1, Grant g2) 
  => ALang t a (Context (g1,g2)) 
  -> ALang t a (Context g1, Context g2)
tup2Ctx m = tup22 (m >>> deconA) $ \((s1,s2),(g1,g2)) ->
  eform conA (s1 &&& g1) &&& eform conA (s2 &&& g2)
