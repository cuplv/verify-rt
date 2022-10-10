{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}

module ALang.Internal where

import Data.SBV
import Data.SBV.Either
import Data.SBV.Maybe
import Data.SBV.Tuple
import Symbol

data ALang t a b where
  ASequenceLR
    :: (Avs a, Avs b, Avs c)
    => ALang t a b -> ALang t b c -> ALang t a c
  ATuple2
    :: (Avs a1, Avs b1, Avs a2, Avs b2)
    => ALang t a1 b1 -> ALang t a2 b2 -> ALang t (a1,a2) (b1,b2)
  AEither
    :: (Avs a, Avs b, Avs la, Avs lb, Avs ra, Avs rb)
    => ALang t (a,la) (b,lb) -- Left case
    -> ALang t (a,ra) (b,rb) -- Right case
    -> ALang t (a, Either la ra) (b, Either lb rb)
  AMaybe
    :: (Avs a, Avs b, Avs c, Avs d)
    => ALang t (a,b) (c,d) -- Just case
    -> ALang t a c -- Nothing case
    -> ALang t (a, Maybe b) (c, Maybe d)
  ABool
    :: (Avs a, Avs b)
    => ALang t a b -- true branch
    -> ALang t a b -- false branch
    -> ALang t (a,Bool) (b,Bool)
  ArrF :: (Avs a, Avs b) => FSpec a b -> (a -> b) -> ALang t a b
  ArrP :: (Avs a, Avs b) => PSpec a b -> (a -> b) -> ALang t a b
  FxTerm :: (Avs a, Avs b) => t a b -> ALang t a b
data NoFx a b

noFx :: Fun a b -> ALang t a b
noFx a = case a of
  ASequenceLR a1 a2 -> ASequenceLR (noFx a1) (noFx a2)
  ATuple2 a1 a2 -> ATuple2 (noFx a1) (noFx a2)
  AEither a1 a2 -> AEither (noFx a1) (noFx a2)
  AMaybe a1 a2 -> AMaybe (noFx a1) (noFx a2)
  ABool a1 a2 -> ABool (noFx a1) (noFx a2)
  ArrF s f -> ArrF s f
  ArrP p f -> ArrP p f

type Fun a b = ALang NoFx a b

runFun :: Fun a b -> a -> b
runFun m = case m of
  ASequenceLR ml mr -> runFun mr . runFun ml
  ATuple2 m1 m2 -> \(a,b) -> (runFun m1 a, runFun m2 b)
  AEither ml mr -> \(a,b) -> case b of
    Left bl ->
      let (a1,b1) = runFun ml (a,bl)
      in (a1, Left b1)
    Right br ->
      let (a1,b1) = runFun mr (a,br)
      in (a1, Right b1)
  AMaybe mj mn -> \(a,b) -> case b of
    Just bj ->
      let (a1,b1) = runFun mj (a,bj)
      in (a1, Just b1)
    Nothing -> (runFun mn a, Nothing)
  ABool mt mf -> \(a,b) ->
    let a1 = if b
                then runFun mt a
                else runFun mf a
    in (a1,b)
  ArrF _ f -> f
  ArrP _ f -> f

symbolize :: (Avs a, Avs b) => Fun a b -> FSpec a b
symbolize m a = case m of
  ASequenceLR ml mr -> symbolize ml a >>= symbolize mr
  ATuple2 m1 m2 -> do
    b1 <- symbolize m1 (_1 a)
    b2 <- symbolize m2 (_2 a)
    return $ tuple (b1,b2)
  AEither ml mr -> do
    bl <- do
      b <- symbolize ml $ tuple (_1 a, fromLeft $ _2 a)
      return $ tuple (_1 b, sLeft $ _2 b)
    br <- do
      b <- symbolize mr $ tuple (_1 a, fromRight $ _2 a)
      return $ tuple (_1 b, sRight $ _2 b)
    return $ ite (isLeft $ _2 a) bl br
  AMaybe mj mn -> do
    bj <- do
      b <- symbolize mj $ tuple (_1 a, fromJust $ _2 a)
      return $ tuple (_1 b, sJust $ _2 b)
    bn <- do
      b <- symbolize mn $ _1 a
      return $ tuple (b, sNothing)
    return $ ite (isJust $ _2 a) bj bn
  ABool mt mf -> do
    bt <- symbolize mt (_1 a)
    bf <- symbolize mf (_1 a)
    return $ tuple (ite (_2 a) bt bf, (_2 a))
  ArrF f _ -> f a
  ArrP p _ -> do
    b <- forall_
    constrain =<< p a b
    return b
