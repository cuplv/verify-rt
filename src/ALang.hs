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

data ALang d a b where
  Id :: (Avs d, Avs a) => ALang d a a
  Fun :: (Avs d, Avs a, Avs b) => (a -> b) -> ALang d a b
  Const :: (Avs d, Avs a, Avs b) => b -> ALang d a b
  PipeRL
    :: (Avs d, Avs a, Avs b, Avs c)
    => ALang d b c -> ALang d a b -> ALang d a c
  ATimes
    :: (Avs d, Avs a1, Avs b1, Avs a2, Avs b2)
    => ALang d a1 b1 -> ALang d a2 b2 -> ALang d (a1,a2) (b1,b2)
  ASum
    :: (Avs d, Avs a1, Avs b1, Avs a2, Avs b2)
    => ALang d a1 b1
    -> ALang d a2 b2
    -> ALang d (Either a1 a2) (Either b1 b2)
  Split :: (Avs d, Avs a) => ALang d a (a,a)
  TakeL :: (Avs d, Avs a1, Avs a2) => ALang d (a1,a2) a1
  TakeR :: (Avs d, Avs a1, Avs a2) => ALang d (a1,a2) a2
  Join :: (Avs d, Avs a) => ALang d (Either a a) a
  Flip :: (Avs d, Avs a1, Avs a2) => ALang d (a1,a2) (a2,a1)
  DistL
    :: (Avs d, Avs a1, Avs a2, Avs a3)
    => ALang d (a1, Either a2 a3) (Either (a1, a2) (a1, a3))

  GetState :: (Avs d, Avs a) => ALang d a d
  VdTerm :: (ValDomain l, Avs d, Avs a, Avs b) => l a b -> ALang d a b
  SvTerm :: (Service v, Avs d, Avs a, Avs b) => v d a b -> ALang d a b

(<<<) :: (Avs d, Avs a, Avs b, Avs c) => ALang d b c -> ALang d a b -> ALang d a c
(<<<) = PipeRL

(>>>) :: (Avs d, Avs a, Avs b, Avs c) => ALang d a b -> ALang d b c -> ALang d a c
(>>>) = flip PipeRL

leftA 
  :: (Avs d, Avs a1, Avs a2, Avs b1) 
  => ALang d a1 b1
  -> ALang d (Either a1 a2) (Either b1 a2)
leftA m = ASum m Id

rightA
  :: (Avs d, Avs a1, Avs a2, Avs b2) 
  => ALang d a2 b2
  -> ALang d (Either a1 a2) (Either a1 b2)
rightA m = ASum Id m

(>?>) m1 m2 = m1 >>> rightA m2

infixl 8 >?>

(>!>) m1 m2 = m1 >>> leftA m2

infixl 8 >!>

firstA
  :: (Avs d, Avs a1, Avs a2, Avs b)
  => ALang d a1 b
  -> ALang d (a1,a2) (b,a2)
firstA a = ATimes a Id

secondA
  :: (Avs d, Avs a1, Avs a2, Avs b)
  => ALang d a2 b
  -> ALang d (a1,a2) (a1,b)
secondA a = ATimes Id a

interpret :: ALang d a b -> a -> b
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
  :: (Avs d, Avs a, Avs b)
  => ALang d a b
  -> Sy d
  -> Sy a
  -> Symbolic (Sy d, Sy b)
symbolize m d a = case m of
  Id -> return (d, a)
  Fun _ -> (,) d <$> exists_
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

checkSpec :: (Avs d, Avs a, Avs b) => ALang d a b -> TSpec d a b -> IO Bool
checkSpec tr (TSpec i m) = do
  r <- prove $ \d1 a -> do
    (d2, b) <- symbolize tr d1 a
    let ps = i a
        ms = m d1 a d2 b
    return (ps .=> ms)
  case r of
    ThmResult (Unsatisfiable _ _) -> return True
    ThmResult (Satisfiable _ _) -> return False
    _ -> error (show r)
