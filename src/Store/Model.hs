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
  mkIdU :: Fun () u
  seqU :: u -> Fun (u,u) u
  applyU :: u -> Fun (u, UState u) (UState u)
  symU :: u -> Sy u -> Sy (UState u) -> Symbolic (Sy (UState u))
  symU z u s = symbolize (applyU z) (tuple (u,s))

idU :: (Avs a, Update u) => Fun a u
idU = forget >>> mkIdU

seqE :: (Avs a, Update u) => u -> Fun a u -> Fun a u -> Fun a u
seqE uw m1 m2 = (m1 &&& m2) >>> seqU uw

instance Update () where
  type UState () = ()
  mkIdU = ca ()
  seqU _ = ca ()
  applyU _ = ca ()

data NoUpd s = NoUpd deriving (Show,Eq,Ord)

instance Avs (NoUpd s) where
  type Rep (NoUpd s) = ()

instance Avc (NoUpd s) where
  toRep _ = return su
  repc _ _ = sTrue

instance (Avs s) => Update (NoUpd s) where
  type UState (NoUpd s) = s
  mkIdU = ca NoUpd
  seqU _ = ca NoUpd
  applyU _ = tup2g2

instance (Update a, Update b) => Update (a,b) where
  type UState (a,b) = (UState a, UState b)
  mkIdU = mkIdU &&& mkIdU
  seqU (aw,bw) =
    tup2 $ \u1 u2 ->
    tup2' u1 $ \a1 b1 ->
    tup2' u2 $ \a2 b2 ->
    seqE aw a1 a2 &&& seqE bw b1 b2
  applyU (aw,bw) =
    tup22 idA $ \((ua,ub), (sa,sb)) ->
    eform2 (applyU aw) ua sa
    &&& eform2 (applyU bw) ub sb

instance (Update a, Update b, Update c) => Update (a,b,c) where
  type UState (a,b,c) = (UState a, UState b, UState c)
  mkIdU = mktup3 mkIdU mkIdU mkIdU
  seqU (aw,bw,cw) =
    tup2 $ \u1 u2 ->
    tup3' u1 $ \a1 b1 c1 ->
    tup3' u2 $ \a2 b2 c2 ->
    mktup3 (seqE aw a1 a2) (seqE bw b1 b2) (seqE cw c1 c2)
  applyU (aw,bw,cw) =
    tup23 idA $ \((ua,ub,uc), (sa,sb,sc)) ->
    mktup3
      (eform2 (applyU aw) ua sa)
      (eform2 (applyU bw) ub sb)
      (eform2 (applyU cw) uc sc)

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

instance (Grant a, Grant b, Grant c) => Grant (a,b,c) where
  type GUpd (a,b,c) = (GUpd a, GUpd b, GUpd c)
  readG (aw,bw,cw) g s1 s2 = do
    a <- readG aw (_1 g) (_1 s1) (_1 s2) 
    b <- readG bw (_2 g) (_2 s1) (_2 s2)
    c <- readG cw (_3 g) (_3 s1) (_3 s2)
    return (a .&& b .&& c)
  writeG (aw,bw,cw) g s1 s2 = do
    a <- writeG aw (_1 g) (_1 s1) (_1 s2) 
    b <- writeG bw (_2 g) (_2 s1) (_2 s2) 
    c <- writeG cw (_3 g) (_3 s1) (_3 s2) 
    return (a .&& b .&& c)
  useG = undefined

data Context g
  = Context { ctxState :: GState g
            , ctxGrant :: g
            }

instance (Grant g) => Avs (Context g) where
  type Rep (Context g) = (Rep (GState g), Rep g)

instance (Grant g, Avc g, Avc (UState (GUpd g))) => Avc (Context g) where
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

tup3Ctx 
  :: (Avs a, Grant g1, Grant g2, Grant g3) 
  => ALang t a (Context (g1,g2,g3)) 
  -> ALang t a (Context g1, Context g2, Context g3)
tup3Ctx m = tup23 (m >>> deconA) $ \((s1,s2,s3),(g1,g2,g3)) ->
  undefined
  -- mktup3
  --   (eform conA (s1 &&& g1))
  --   (eform conA (s2 &&& g2))
  --   (eform conA (s3 &&& g3))
