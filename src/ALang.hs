{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}

module ALang where

import Symbol
import ValDomain

import Data.SBV
import Data.SBV.Tuple
import Data.SBV.Either

data ALang a b where
  Id :: (Avs a) => ALang a a
  Fun :: (Avs a, Avs b) => (a -> b) -> ALang a b
  Const :: (Avs b) => b -> ALang () b
  PipeRL
    :: (Avs a, Avs b, Avs c)
    => ALang b c -> ALang a b -> ALang a c
  ATimes
    :: (Avs a1, Avs b1, Avs a2, Avs b2)
    => ALang a1 b1 -> ALang a2 b2 -> ALang (a1,a2) (b1,b2)
  ASum
    :: (Avs a1, Avs b1, Avs a2, Avs b2)
    => ALang a1 b1
    -> ALang a2 b2
    -> ALang (Either a1 a2) (Either b1 b2)

  Split :: (Avs a) => ALang a (a,a)
  Flip :: (Avs a1, Avs a2) => ALang (a1,a2) (a2,a1)
  Take :: (Avs a1, Avs a2) => ALang (a1,a2) a1

  Alt :: (Avs a1, Avs a2) => ALang a1 (Either a1 a2)
  Swap :: (Avs a1, Avs a2) => ALang (Either a1 a2) (Either a2 a1)
  Join :: (Avs a) => ALang (Either a a) a

  Dist
    :: (Avs a1, Avs a2, Avs a3)
    => ALang (a1, Either a2 a3) (Either (a1, a2) (a1, a3))
  UnDist
    :: (Avs a1, Avs a2, Avs a3)
    => ALang (Either (a1, a2) (a1, a3)) (a1, Either a2 a3)

  Forget :: (Avs a) => ALang a ()

  VdTerm :: (Avs a, Avs b, ValDomain v) => v a b -> ALang a b

(<<<) :: (Avs a, Avs b, Avs c) => ALang b c -> ALang a b -> ALang a c
(<<<) = PipeRL

(>>>) :: (Avs a, Avs b, Avs c) => ALang a b -> ALang b c -> ALang a c
(>>>) = flip PipeRL

(&&&)
  :: (Avs a, Avs b1, Avs b2)
  => ALang a b1
  -> ALang a b2
  -> ALang a (b1,b2)
(&&&) a1 a2 = Split >>> ATimes a1 a2

leftA 
  :: (Avs a1, Avs a2, Avs b1) 
  => ALang a1 b1
  -> ALang (Either a1 a2) (Either b1 a2)
leftA m = ASum m Id

rightA
  :: (Avs a1, Avs a2, Avs b2) 
  => ALang a2 b2
  -> ALang (Either a1 a2) (Either a1 b2)
rightA m = ASum Id m

(>?>) m1 m2 = m1 >>> rightA m2

infixl 8 >?>

(>!>) m1 m2 = m1 >>> leftA m2

infixl 8 >!>

firstA
  :: (Avs a1, Avs a2, Avs b)
  => ALang a1 b
  -> ALang (a1,a2) (b,a2)
firstA a = ATimes a Id

secondA
  :: (Avs a1, Avs a2, Avs b)
  => ALang a2 b
  -> ALang (a1,a2) (a1,b)
secondA a = ATimes Id a

interpret :: ALang a b -> a -> b
interpret m a = case (m,a) of
  (Id, a) -> a
  (Fun f, a) -> f a
  (Const n, _) -> n
  (PipeRL ml mr, a) -> interpret ml $ interpret mr a
  (ATimes m1 m2, (a1,a2)) -> (interpret m1 a1, interpret m2 a2)
  (ASum m1 _, Left a1) -> Left (interpret m1 a1)
  (ASum _ m2, Right a2) -> Right (interpret m2 a2)
  (Split, a) -> (a,a)
  (Take, a) -> fst a
  (Join, Right a) -> a
  (Join, Left a) -> a

symbolize
  :: (Avs a, Avs b)
  => ALang a b
  -> Sy a
  -> Symbolic (Sy b)
symbolize m a = case m of
  Id -> return a
  Fun _ -> forall_
  Const x -> return (literal $ toRep x)
  PipeRL ml mr -> do
    b <- symbolize mr a
    symbolize ml b
  ATimes m1 m2 -> do 
    b1 <- symbolize m1 (_1 a)
    b2 <- symbolize m2 (_2 a)
    return (tuple (b1, b2))
  ASum ml mr -> do
    bl <- symbolize ml (fromLeft a)
    br <- symbolize mr (fromRight a)
    let b = Data.SBV.Either.either (const $ sLeft bl) (const $ sRight br) a
    return b
  Split -> return (tuple (a,a))
  Flip -> return (tuple (_2 a, _1 a))
  Take -> return (_1 a)
  Join -> return (Data.SBV.Either.either id id a)
  Dist -> 
    let b = bimap
              (\al -> tuple (_1 a, al))
              (\ar -> tuple (_1 a, ar))
              (_2 a)
    in return b
