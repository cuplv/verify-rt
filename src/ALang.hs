{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}

module ALang where

import Service
import Symbol
import ValDomain

import Data.SBV
import Data.SBV.Tuple
import Data.SBV.Either

data ALang v a b where
  Id :: (Avs a) => ALang v a a
  Fun :: (Avs a, Avs b) => (a -> b) -> ALang v a b
  Const :: (Avs b) => b -> ALang v a b
  PipeRL
    :: (Avs a, Avs b, Avs c)
    => ALang v b c -> ALang v a b -> ALang v a c
  ATimes
    :: (Avs a1, Avs b1, Avs a2, Avs b2)
    => ALang v a1 b1 -> ALang v a2 b2 -> ALang v (a1,a2) (b1,b2)
  ASum
    :: (Avs a1, Avs b1, Avs a2, Avs b2)
    => ALang v a1 b1
    -> ALang v a2 b2
    -> ALang v (Either a1 a2) (Either b1 b2)
  Split :: (Avs a) => ALang v a (a,a)
  TakeL :: (Avs a1, Avs a2) => ALang v (a1,a2) a1
  TakeR :: (Avs a1, Avs a2) => ALang v (a1,a2) a2
  AssumeL :: (Avs a1, Avs a2) => ALang v (Either a1 a2) a1
  AssumeR :: (Avs a1, Avs a2) => ALang v (Either a1 a2) a2
  Join :: (Avs a) => ALang v (Either a a) a
  Flip :: (Avs a1, Avs a2) => ALang v (a1,a2) (a2,a1)
  DistL
    :: (Avs a1, Avs a2, Avs a3)
    => ALang v (a1, Either a2 a3) (Either (a1, a2) (a1, a3))

  GetState :: (Service v) => ALang v a (SvState v)
  VdTerm :: (ValDomain l, Avs a, Avs b) => l a b -> ALang v a b
  SvTerm :: (Service v, Avs a, Avs b) => v a b -> ALang v a b

(<<<) :: (Avs a, Avs b, Avs c) => ALang v b c -> ALang v a b -> ALang v a c
(<<<) = PipeRL

(>>>) :: (Avs a, Avs b, Avs c) => ALang v a b -> ALang v b c -> ALang v a c
(>>>) = flip PipeRL

leftA 
  :: (Avs a1, Avs a2, Avs b1) 
  => ALang v a1 b1
  -> ALang v (Either a1 a2) (Either b1 a2)
leftA m = ASum m Id

rightA
  :: (Avs a1, Avs a2, Avs b2) 
  => ALang v a2 b2
  -> ALang v (Either a1 a2) (Either a1 b2)
rightA m = ASum Id m

(>?>) m1 m2 = m1 >>> rightA m2

infixl 8 >?>

(>!>) m1 m2 = m1 >>> leftA m2

infixl 8 >!>

firstA
  :: (Avs a1, Avs a2, Avs b)
  => ALang v a1 b
  -> ALang v (a1,a2) (b,a2)
firstA a = ATimes a Id

secondA
  :: (Avs a1, Avs a2, Avs b)
  => ALang v a2 b
  -> ALang v (a1,a2) (a1,b)
secondA a = ATimes Id a

interpret :: ALang v a b -> a -> b
interpret m a = case (m,a) of
  (Id, a) -> a
  (Fun f, a) -> f a
  (Const n, _) -> n
  (PipeRL ml mr, a) -> interpret ml $ interpret mr a
  (ATimes m1 m2, (a1,a2)) -> (interpret m1 a1, interpret m2 a2)
  (ASum m1 _, Left a1) -> Left (interpret m1 a1)
  (ASum _ m2, Right a2) -> Right (interpret m2 a2)
  (Split, a) -> (a,a)
  (TakeL, a) -> fst a
  (TakeR, a) -> snd a
  (Join, Right a) -> a
  (Join, Left a) -> a

symbolize
  :: (Service v, Avs a, Avs b)
  => ALang v a b
  -> Sy (SvState v)
  -> Sy a
  -> Symbolic (Sy (SvState v), Sy b)
symbolize m d a = case m of
  Id -> return (d, a)
  Fun _ -> (,) d <$> forall_
  Const x -> return (d, literal $ toRep x)
  PipeRL ml mr -> do
    (d', b) <- symbolize mr d a
    symbolize ml d' b
  ATimes m1 m2 -> do 
    (d', b1) <- symbolize m1 d (_1 a)
    (d'', b2) <- symbolize m2 d' (_2 a)
    return (d'', tuple (b1, b2))
  ASum ml mr -> do
    (dl, bl) <- symbolize ml d (fromLeft a)
    (dr, br) <- symbolize mr d (fromRight a)
    let d' = Data.SBV.Either.either (const dl) (const dr) a
        b = Data.SBV.Either.either (const $ sLeft bl) (const $ sRight br) a
    return (d', b)
  Split -> return (d, tuple (a,a))
  TakeL -> return (d, _1 a)
  TakeR -> return (d, _2 a)
  AssumeL -> return (d, fromLeft a)
  AssumeR -> return (d, fromRight a)
  Join -> return (d, Data.SBV.Either.either id id a)
  Flip -> return (d, tuple (_2 a, _1 a))
  DistL -> 
    let b = bimap
              (\al -> tuple (_1 a, al))
              (\ar -> tuple (_1 a, ar))
              (_2 a)
    in return (d, b)

  VdTerm l -> do
    let VSpec m = vdSymbol l
    (,) d <$> m a

  SvTerm v -> do
    let SSpec m = svSymbol v
    m d a

checkSpec :: (Service v, Avs a, Avs b) => ALang v a b -> TSpec (SvState v) a b -> IO Bool
checkSpec tr (TSpec m) = do
  r <- prove $ \d1 a -> do
    (d2, b) <- symbolize tr d1 a
    m d1 a d2 b
  case r of
    ThmResult (Unsatisfiable _ _) -> return True
    ThmResult (Satisfiable _ _) -> return False
    _ -> error (show r)
