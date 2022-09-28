{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

module ALang.Base where

import ALang.Internal
import Symbol

import Data.SBV
import Data.SBV.Either
import qualified Data.SBV.Maybe as SM
import Data.SBV.Tuple

-- Operators

(<<<) :: (Avs a, Avs b, Avs c) => ALang t b c -> ALang t a b -> ALang t a c
(<<<) = PipeRL

(>>>) :: (Avs a, Avs b, Avs c) => ALang t a b -> ALang t b c -> ALang t a c
(>>>) = flip PipeRL

(>>|) :: (Avs a, Avs b, Avs c) => ALang t a b -> ALang t () c -> ALang t a c
(>>|) t1 t2 = t1 >>> forget >>> t2

(***)
  :: (Avs a1, Avs a2, Avs b1, Avs b2)
  => ALang t a1 b1
  -> ALang t a2 b2
  -> ALang t (a1,a2) (b1,b2)
(***) = ATimes

(&&&)
  :: (Avs a, Avs b1, Avs b2)
  => ALang t a b1
  -> ALang t a b2
  -> ALang t a (b1,b2)
(&&&) a1 a2 = forkA >>> ATimes a1 a2

(+++)
  :: (Avs a, Avs b, Avs c, Avs d)
  => ALang t a b
  -> ALang t c d
  -> ALang t (Either a c) (Either b d)
(+++) = ASum

(|||)
  :: (Avs a, Avs b, Avs c)
  => ALang t a c
  -> ALang t b c
  -> ALang t (Either a b) c
(|||) ml mr = ASum ml mr >>> selectA

-- Fundamental

idA :: (Avs a) => ALang t a a
idA = Arr return id

funA :: (Avs a, Avs b) => (a -> b) -> ALang t a b
funA  = Arr (const forall_)

constA :: (Avs a, Avs b) => b -> ALang t a b
constA b = Arr (const . return . literal $ toRep b) (const b)

forget :: (Avs a) => ALang t a ()
forget = constA ()

-- Bools

andAllA :: (Avs a) => [Fun a Bool] -> ALang t a Bool
andAllA ts = Arr
  (\a -> do bs <- mapM (\t -> symbolize t a) ts
            return $ foldr (.&&) sTrue bs)
  (\a -> and (map (\t -> runFun t a) ts))

-- Tuples

tup2t3 :: (Avs a, Avs b, Avs c) => ALang t ((a,b),c) (a,b,c)
tup2t3 = Arr (\a -> return $ tuple (_1 (_1 a), _2 (_1 a), _2 a))
             (\((a,b),c) -> (a,b,c))

tup3t2 :: (Avs a, Avs b, Avs c) => ALang t (a,b,c) ((a,b),c)
tup3t2 = Arr (\a -> return $ tuple (tuple (_1 a, _2 a), _3 a))
             (\(a,b,c) -> ((a,b),c))

forkA :: (Avs a) => ALang t a (a,a) 
forkA = Arr (\a -> return $ tuple (a,a)) (\a -> (a,a))

flipA :: (Avs a, Avs b) => ALang t (a,b) (b,a)
flipA = Arr (\a -> return $ tuple (_2 a, _1 a)) (\(a,b) -> (b,a))

class Get1 x a where
  get1 :: ALang t x a

instance (Avs a, Avs b) => Get1 (a,b) a where
  get1 = Arr (return . _1) fst


class Get2 x a where
  get2 :: ALang t x a

instance (Avs a, Avs b) => Get2 (a,b) b where
  get2 = Arr (return . _2) snd


class Set1 x y a where
  set1 :: ALang t (a,x) y 

instance (Avs a, Avs b, Avs c) => Set1 (a,b) (c,b) c where
  set1 = Arr (\a -> return $ tuple (_1 a, _2 (_2 a))) (\(a,(_,b)) -> (a,b))

class Set2 x y a where
  set2 :: ALang t (a,x) y 

instance (Avs a, Avs b, Avs c) => Set2 (a,b) (a,c) c where
  set2 = Arr (\a -> return $ tuple (_1 (_2 a), _1 a)) (\(a,(b,_)) -> (b,a))

over1
  :: (Avs x, Avs y, Avs a, Avs b, Get1 x a, Set1 x y b)
  => ALang t a b -> ALang t x y
over1 f = forkA >>> ATimes (get1 >>> f) idA >>> set1

tup2g1 :: (Avs a, Avs b) => ALang t (a,b) a
tup2g1 = Arr (return . _1) fst

tup2g2 :: (Avs a, Avs b) => ALang t (a,b) b
tup2g2 = Arr (return . _2) snd

fstA :: (Avs a, Avs b, Avs c) => ALang t a b -> ALang t (a,c) (b,c)
fstA = over1

over2
  :: (Avs x, Avs y, Avs a, Avs b, Get2 x a, Set2 x y b)
  => ALang t a b -> ALang t x y
over2 f = forkA >>> ATimes (get2 >>> f) idA >>> set2

sndA :: (Avs a, Avs b, Avs c) => ALang t b c -> ALang t (a,b) (a,c)
sndA = over2

tup3g1 :: (Avs a, Avs b, Avs c) => ALang t (a,b,c) a
tup3g1 = tup3t2 >>> tup2g1 >>> tup2g1

tup3g2 :: (Avs a, Avs b, Avs c) => ALang t (a,b,c) b
tup3g2 = tup3t2 >>> tup2g1 >>> tup2g2

tup3g3 :: (Avs a, Avs b, Avs c) => ALang t (a,b,c) c
tup3g3 = tup3t2 >>> tup2g2

-- Either

instance AFunctor Maybe where
  fmapA = onJust

instance AApplicative Maybe where
  pureA = asJust
  bothA = (m2eA *** m2eA) >>> bothA >>> e2mA

instance AMonad Maybe where
  bindA f = m2eA >>> (constA Nothing ||| f)

instance (Avs e) => AFunctor (Either e) where
  fmapA = onRight

instance (Avs e) => AApplicative (Either e) where
  pureA = asRight
  bothA = distA 
    -- Either (Either e a, e) (Either e a, b)
    >>> onLeft getLeft
    -- Either e (Either e a, b)
    >>> onRight (flipA >>> distA >>> onLeft tup2g2)
    -- Either e (Either e (a,b))
    >>> (asLeft ||| onRight flipA)

instance (Avs e) => AMonad (Either e) where
  bindA f = asLeft ||| f

getLeft :: (Avs a, Avs b) => ALang t (Either a b, a) a
getLeft = flipA >>> distA >>> (tup2g2 ||| tup2g1)

getRight :: (Avs a, Avs b) => ALang t (Either a b, b) b
getRight = flipA >>> distA >>> (tup2g1 ||| tup2g2)

asLeft :: (Avs a, Avs b) => ALang t a (Either a b)
asLeft = Arr (\a -> return $ sLeft a) Left

asRight :: (Avs a, Avs b) => ALang t b (Either a b)
asRight = Arr (\a -> return $ sRight a) Right

onLeft :: (Avs a, Avs b, Avs c) => ALang t a b -> ALang t (Either a c) (Either b c)
onLeft f = ASum f idA

onRight :: (Avs a, Avs b, Avs c) => ALang t b c -> ALang t (Either a b) (Either a c)
onRight f = ASum idA f

-- bindA
--   :: (Avs a, Avs b, Avs e)
--   => ALang t a (Either e b)
--   -> ALang t (Either e a) (Either e b)
-- bindA f = asLeft ||| f

flattenA
  :: (Avs a, Avs e)
  => ALang t (Either e (Either e a)) (Either e a)
flattenA = undefined

selectA :: (Avs a) => ALang t (Either a a) a
selectA = Arr (\a -> return $ Data.SBV.Either.either id id a)
              (\m -> case m of
                       Right a -> a
                       Left a -> a)

distA :: (Avs a, Avs b, Avs c) => ALang t (a, Either b c) (Either (a,b) (a,c)) 
distA = Arr f1 f2
  where f1 a = return $ bimap
                          (\al -> tuple (_1 a, al))
                          (\ar -> tuple (_1 a, ar))
                          (_2 a)

        f2 (a, Left b) = Left (a,b)
        f2 (a, Right c) = Right (a,c)

undistA :: (Avs a, Avs b, Avs c) => ALang t (Either (a,b) (a,c)) (a, Either b c)
undistA = (ASum get1 get1 >>> selectA) &&& ASum get2 get2

b2eA :: ALang t Bool (Either () ())
b2eA = Arr (\a -> return (ite a (sRight su) (sLeft su)))
           (\a -> if a
                     then Right ()
                     else Left ())

e2bA :: (Avs a, Avs b) => ALang t (Either a b) Bool
e2bA = ASum (constA False) (constA True) >>> selectA

asJust :: (Avs a) => ALang t a (Maybe a)
asJust = Arr (\a -> return $ SM.sJust a) Just

fromJust :: (Avs a) => a -> ALang t (Maybe a) a
fromJust a = m2eA >>> ASum (constA a) idA >>> selectA

m2eA :: (Avs a) => ALang t (Maybe a) (Either () a)
m2eA = Arr (return . SM.maybe (literal (Left ())) sRight)
           (\m -> case m of
                    Just a -> Right a
                    Nothing -> Left ())

e2mA :: (Avs a, Avs b) => ALang t (Either a b) (Maybe b)
e2mA = Arr (return . Data.SBV.Either.either (\_ -> literal Nothing) SM.sJust)
           (\m -> case m of
                    Left _ -> Nothing
                    Right a -> Just a)

onJust :: (Avs a, Avs b) => ALang t a b -> ALang t (Maybe a) (Maybe b)
onJust f = m2eA >>> ASum idA f >>> e2mA

-- Ints

sumA :: ALang t (Int,Int) Int
sumA = Arr (\a -> return (_1 a + _2 a)) (\(a,b) -> a + b)

diffA :: ALang t (Int,Int) Int
diffA = over2 negateA >>> sumA

plusA :: Int -> ALang t Int Int
plusA n = idA &&& constA n >>> sumA

minusA :: Int -> ALang t Int Int
minusA n = idA &&& constA n >>> diffA

negateA :: ALang t Int Int
negateA = Arr (\a -> return (-a)) (\a -> (-a))

leA :: ALang t (Int,Int) Bool
leA = Arr (\a -> return $ _1 a .<= _2 a) (\(a,b) -> a <= b)

geA :: ALang t (Int,Int) Bool
geA = Arr (\a -> return $ _1 a .>= _2 a) (\(a,b) -> a >= b)

-- Datatype construction

class (Avs d, (Avs (Content d))) => AData d where
  type Content d
  conA :: ALang t (Content d) d
  deconA :: ALang t d (Content d)

-- Monad stack

class AFunctor m where
  fmapA :: (Avs a, Avs b, Avs (m a), Avs (m b))
        => ALang t a b -> ALang t (m a) (m b)

(<$>>) :: (AFunctor m, Avs a, Avs b, Avs c, Avs (m b), Avs (m c))
       => ALang t a (m b) -> ALang t b c -> ALang t a (m c)
(<$>>) f g = f >>> fmapA g

class (AFunctor m) => AApplicative m where
  pureA :: (Avs a, Avs (m a)) => ALang t a (m a)
  bothA :: (Avs a, Avs b, Avs (m a), Avs (m b), Avs (m (a,b)))
        => ALang t (m a, m b) (m (a,b))
  liftA2A :: (Avs a, Avs b, Avs c, Avs (m a), Avs (m b), Avs (m c), Avs (m (a,b)))
          => ALang t (a,b) c -> ALang t (m a, m b) (m c)
  liftA2A f = bothA >>> fmapA f

class (AApplicative m) => AMonad m where
  bindA :: (Avs a, Avs b, Avs (m a), Avs (m b))
        => ALang t a (m b) -> ALang t (m a) (m b)

(>>=>) :: (AMonad m, Avs a, Avs b, Avs c, Avs (m a), Avs (m b), Avs (m c))
       => ALang t a (m b) -> ALang t b (m c) -> ALang t a (m c)
(>>=>) f g = f >>> bindA g
