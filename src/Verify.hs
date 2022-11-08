module Verify where

import ALang
import Store.Model
import Symbol

import Data.SBV
import qualified Data.SBV.Maybe as SM
import Data.SBV.Tuple

type TransactS g
  = Sy (Context g) -> Sy (GState g) -> Symbolic (Sy (GState g))

type Spec g = Binr (Sy (GState g))

trueSpec :: (SymVal s) => Binr (SBV s)
trueSpec _ _ = pure sTrue

tup2Spec :: (SymVal s1, SymVal s2) => (Binr (SBV s1), Binr (SBV s2)) -> Binr (SBV (s1,s2))
tup2Spec (p1,p2) = \a b ->
  (.&&) <$> p1 (_1 a) (_1 b) <*> p2 (_2 a) (_2 b)

tup3Spec :: (SymVal s1, SymVal s2, SymVal s3) => (Binr (SBV s1), Binr (SBV s2), Binr (SBV s3)) -> Binr (SBV (s1,s2,s3))
tup3Spec (p1,p2,p3) = \a b -> do
  r1 <- p1 (_1 a) (_1 b)
  r2 <- p2 (_2 a) (_2 b)
  r3 <- p3 (_3 a) (_3 b)
  return $ r1 .&& r2 .&& r3

gPrePost
  :: (Grant g)
  => g
  -> TransactS g
  -> Spec g
  -> Symbolic (Sy g, Sy (GState g), Sy (GState g))
gPrePost z t p = do
  ctx <- forall "context"
  pre <- forall "pre"
  constrain =<< p (stateS ctx) pre
  constrain =<< readCtx z ctx pre

  post <- t ctx pre

  return (grantS ctx,pre,post)

tsSpec
  :: (Grant g)
  => g
  -> TransactS g
  -> Spec g
  -> Symbolic SBool
tsSpec z t p = do
  (_,pre,post) <- gPrePost z t p
  p pre post

tsWrite
  :: (Grant g)
  => g
  -> TransactS g
  -> Spec g
  -> Symbolic SBool
tsWrite z t p = do
  (g,pre,post) <- gPrePost z t p
  writeG z g pre post

-- symT
--   :: (Capability k, Avs w, Avs b)
--   => Transact' k w b
--   -> (Sy (UState (KUpd k)), Sy k, Sy k)
--   -> Sy w
--   -> Symbolic (Sy (Maybe (KUpd k, b)))
-- symT f (s,e,c) w = do
--   symbolize f $ tuple (tuple (s,e,c), w)

-- stateSpec
--   :: (Capability k, Avs w, Avs b)
--   => (k, KUpd k)
--   -> Transact' k w b
--   -> (Sy w -> Symbolic SBool)
--   -> (Sy (KState k) -> Sy (KState k) -> Symbolic SBool)
--   -> Symbolic SBool
-- stateSpec (y,z) f wo o = do
--   w <- forall "w"
--   constrain =<< wo w
--   s <- forall "local state"
--   env <- forall "env"
--   constrain $ constrainC y env
--   cap <- forall "cap"
--   constrain $ constrainC y cap

--   sPre <- forall "pre state"
--   constrain =<< reachC y env s sPre
--   constrain =<< o s sPre

--   r <- symT f (s,env,cap) w
--   let u = _1 (SM.fromJust r)
--       b = _2 (SM.fromJust r)

--   sPost <- forall "post state"
--   constrain =<< symU z u s sPost
 
--   result <- o sPre sPost
--   return $ SM.maybe sTrue (const result) r

-- capSpec
--   :: (Capability k, Avs w, Avs b)
--   => (k, KUpd k)
--   -> Transact' k w b
--   -> (Sy w -> Symbolic SBool)
--   -> Symbolic SBool
-- capSpec (y,z) f wo = do
--   w <- forall "w"
--   constrain =<< wo w
--   s <- forall "local state"
--   env <- forall "env"
--   constrain $ constrainC y env
--   cap <- forall "cap"
--   constrain $ constrainC y cap

--   r <- symT f (s,env,cap) w

--   let u = _1 (SM.fromJust r)
--       b = _2 (SM.fromJust r)

--   sPre <- forall "pre state"
--   sPost <- forall "post state"
--   constrain =<< symU z u sPre sPost

--   result <- reachC y cap sPre sPost
--   return $ SM.maybe sTrue (const result) r

-- safeTr
--   :: (Capability k, Avs w, Avs b)
--   => (k, KUpd k)
--   -> Transact' k w b
--   -> (Sy w -> Symbolic SBool)
--   -> (Sy (KState k) -> Sy (KState k) -> Symbolic SBool)
--   -> Symbolic SBool
-- safeTr x f wo p = do
--   r1 <- stateSpec x f wo p
--   r2 <- capSpec x f wo
--   return (r1 .&& r2) 
