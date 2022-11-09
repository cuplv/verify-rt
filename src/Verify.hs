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
