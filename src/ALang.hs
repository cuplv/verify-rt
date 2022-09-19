{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}

module ALang where

import Symbol
import ValDomain

import Data.SBV
import Data.SBV.Tuple
import Data.SBV.Either

type FxSpec t a b = (Sy (FxRep t), Sy a) -> Symbolic (Sy (FxRep t), Sy b)

class (Avs (FxRep t)) => Fx t where
  type FxRep t :: *
  fxSym :: (Avs a, Avs b) => t a b -> FxSpec t a b

data NoFx a b

instance Fx NoFx where
  type FxRep NoFx = ()
  fxSym = undefined

type ALang' a b = ALang NoFx a b

data ALang t a b where
  Id :: (Avs a) => ALang t a a
  Fun :: (Avs a, Avs b) => (a -> b) -> ALang t a b
  Const :: (Avs b) => b -> ALang t () b
  PipeRL
    :: (Avs a, Avs b, Avs c)
    => ALang t b c -> ALang t a b -> ALang t a c
  ATimes
    :: (Avs a1, Avs b1, Avs a2, Avs b2)
    => ALang t a1 b1 -> ALang t a2 b2 -> ALang t (a1,a2) (b1,b2)
  ASum
    :: (Avs a1, Avs b1, Avs a2, Avs b2)
    => ALang t a1 b1
    -> ALang t a2 b2
    -> ALang t (Either a1 a2) (Either b1 b2)

  Split :: (Avs a) => ALang t a (a,a)
  Flip :: (Avs a1, Avs a2) => ALang t (a1,a2) (a2,a1)
  Take :: (Avs a1, Avs a2) => ALang t (a1,a2) a1

  Alt :: (Avs a1, Avs a2) => ALang t a1 (Either a1 a2)
  Swap :: (Avs a1, Avs a2) => ALang t (Either a1 a2) (Either a2 a1)
  Join :: (Avs a) => ALang t (Either a a) a

  Dist
    :: (Avs a1, Avs a2, Avs a3)
    => ALang t (a1, Either a2 a3) (Either (a1, a2) (a1, a3))
  UnDist
    :: (Avs a1, Avs a2, Avs a3)
    => ALang t (Either (a1, a2) (a1, a3)) (a1, Either a2 a3)

  Forget :: (Avs a) => ALang t a ()

  VdTerm :: (Avs a, Avs b, ValDomain v) => v a b -> ALang t a b

  FxTerm :: (Fx t, Avs a, Avs b) => t a b -> ALang t a b

(<<<) :: (Avs a, Avs b, Avs c) => ALang t b c -> ALang t a b -> ALang t a c
(<<<) = PipeRL

(>>>) :: (Avs a, Avs b, Avs c) => ALang t a b -> ALang t b c -> ALang t a c
(>>>) = flip PipeRL

(&&&)
  :: (Avs a, Avs b1, Avs b2)
  => ALang t a b1
  -> ALang t a b2
  -> ALang t a (b1,b2)
(&&&) a1 a2 = Split >>> ATimes a1 a2

leftA 
  :: (Avs a1, Avs a2, Avs b1) 
  => ALang t a1 b1
  -> ALang t (Either a1 a2) (Either b1 a2)
leftA m = ASum m Id

rightA
  :: (Avs a1, Avs a2, Avs b2) 
  => ALang t a2 b2
  -> ALang t (Either a1 a2) (Either a1 b2)
rightA m = ASum Id m

(>?>) m1 m2 = m1 >>> rightA m2

infixl 8 >?>

(>!>) m1 m2 = m1 >>> leftA m2

infixl 8 >!>

firstA
  :: (Avs a1, Avs a2, Avs b)
  => ALang t a1 b
  -> ALang t (a1,a2) (b,a2)
firstA a = ATimes a Id

secondA
  :: (Avs a1, Avs a2, Avs b)
  => ALang t a2 b
  -> ALang t (a1,a2) (a1,b)
secondA a = ATimes Id a

interpret :: ALang t a b -> a -> b
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

symbolize :: (Fx t, Avs a, Avs b) => ALang t a b -> FxSpec t a b
symbolize m (s,a) = case m of
  Id -> return (s,a)
  Fun _ -> (,) s <$> forall_
  Const x -> return (s, literal $ toRep x)
  PipeRL ml mr -> do
    (s1,b) <- symbolize mr (s,a)
    symbolize ml (s1,b)
  ATimes m1 m2 -> do 
    (s1,b1) <- symbolize m1 (s, _1 a)
    (s2,b2) <- symbolize m2 (s1, _2 a)
    return (s2, tuple (b1, b2))
  ASum ml mr -> do
    (sl,bl) <- symbolize ml (s, fromLeft a)
    (sr,br) <- symbolize mr (s, fromRight a)
    let s' = Data.SBV.Either.either (const sl) (const sr) a
        b = Data.SBV.Either.either (const $ sLeft bl) (const $ sRight br) a
    return (s',b)
  Split -> return (s, tuple (a,a))
  Flip -> return (s, tuple (_2 a, _1 a))
  Take -> return (s, _1 a)
  Join -> return (s, Data.SBV.Either.either id id a)
  Dist -> 
    let b = bimap
              (\al -> tuple (_1 a, al))
              (\ar -> tuple (_1 a, ar))
              (_2 a)
    in return (s,b)
