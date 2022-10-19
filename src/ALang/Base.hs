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
(<<<) = flip ASequenceLR

(>>>) :: (Avs a, Avs b, Avs c) => ALang t a b -> ALang t b c -> ALang t a c
(>>>) = ASequenceLR

(>>|) :: (Avs a, Avs b, Avs c) => ALang t a b -> ALang t () c -> ALang t a c
(>>|) t1 t2 = t1 >>> forget >>> t2

(***)
  :: (Avs a1, Avs a2, Avs b1, Avs b2)
  => ALang t a1 b1
  -> ALang t a2 b2
  -> ALang t (a1,a2) (b1,b2)
(***) = ATuple2

(&&&)
  :: (Avs a, Avs b1, Avs b2)
  => ALang t a b1
  -> ALang t a b2
  -> ALang t a (b1,b2)
(&&&) a1 a2 = forkA >>> ATuple2 a1 a2

(+++)
  :: (Avs a, Avs b, Avs c, Avs d)
  => ALang t a b
  -> ALang t c d
  -> ALang t (Either a c) (Either b d)
(+++) ml mr =
  tup2c1 ()
  >>> AEither (idA *** ml) (idA *** mr)
  >>> tup2g2

(|||)
  :: (Avs a, Avs b, Avs c)
  => ALang t a c
  -> ALang t b c
  -> ALang t (Either a b) c
(|||) ml mr = (ml +++ mr) >>> selectA

-- Fundamental

idA :: (Avs a) => ALang t a a
idA = ArrF return id

funA :: (Avs a, Avs b) => (a -> b) -> ALang t a b
funA = ArrF (const forall_)

funE :: (Avs x, Avs a, Avs b) => ALang t x a -> (a -> b) -> ALang t x b
funE m f = m >>> funA f

constA :: (Avs a, Avs b) => b -> ALang t a b
constA b = ArrF (const $ toRep b) (const b)

ca :: (Avs a, Avs b) => b -> ALang t a b
ca = constA

forget :: (Avs a) => ALang t a ()
forget = constA ()

passThru :: (Avs a, Avs b) => ALang t a b -> ALang t a a
passThru f = (idA &&& f) >>> tup2g1

eform :: (Avs a, Avs b, Avs c) => ALang t b c -> ALang t a b -> ALang t a c
eform = (<<<)

eform2 
  :: (Avs a, Avs b, Avs c, Avs d)
  => ALang t (b,c) d
  -> ALang t a b
  -> ALang t a c
  -> ALang t a d
eform2 m a1 a2 = (a1 &&& a2) >>> m

-- Bools

andAllA :: (Avs a) => [Fun a Bool] -> ALang t a Bool
andAllA [] = constA True
andAllA (m:ms) = (idA &&& noFx m) >>> iteA (andAllA ms) (constA False)

notE :: (Avs a) => ALang t a Bool -> ALang t a Bool
notE m = m >>> ArrF
  (pure . sNot)
  not

andA :: ALang t (Bool,Bool) Bool
andA = ArrF
  (\a -> return $ _1 a .&& _2 a)
  (\(a,b) -> a && b)

($/\) :: (Avs a) => ALang t a Bool -> ALang t a Bool -> ALang t a Bool
($/\) m1 m2 = (m1 &&& m2) >>> andA

eqA :: (Avs a, Eq a) => ALang t (a,a) Bool
eqA = ArrF
  (\a -> return $ _1 a .== _2 a)
  (\(a,b) -> a == b)

($==) :: (Avs a, Avs b, Eq b) => ALang t a b -> ALang t a b -> ALang t a Bool
($==) m1 m2 = (m1 &&& m2) >>> eqA

iteA :: (Avs a, Avs b) => ALang t a b -> ALang t a b -> ALang t (a,Bool) b
iteA mt mf = ABool mt mf >>> tup2g1

iteA'
  :: (Avs a, Avs b)
  => ALang t a b
  -> ALang t a b
  -> ALang t (a,Bool) (b,Bool)
iteA' = ABool

iteS
  :: (Avs a, Avs b)
  => ALang t a Bool
  -> ALang t a b
  -> ALang t a b
  -> ALang t a b
iteS p mt mf = (idA &&& p) >>> iteA mt mf

assertA
  :: (Avs a, Avs b)
  => ALang t a Bool
  -> ALang t a (Maybe b)
  -> ALang t a (Maybe b)
assertA p t = (idA &&& p) >>> iteA t (constA Nothing)

-- Tuples

tup2t3 :: (Avs a, Avs b, Avs c) => ALang t ((a,b),c) (a,b,c)
tup2t3 = ArrF (\a -> return $ tuple (_1 (_1 a), _2 (_1 a), _2 a))
             (\((a,b),c) -> (a,b,c))

tup3t2 :: (Avs a, Avs b, Avs c) => ALang t (a,b,c) ((a,b),c)
tup3t2 = ArrF (\a -> return $ tuple (tuple (_1 a, _2 a), _3 a))
             (\(a,b,c) -> ((a,b),c))

forkA :: (Avs a) => ALang t a (a,a) 
forkA = ArrF (\a -> return $ tuple (a,a)) (\a -> (a,a))

flipA :: (Avs a, Avs b) => ALang t (a,b) (b,a)
flipA = ArrF (\a -> return $ tuple (_2 a, _1 a)) (\(a,b) -> (b,a))

class Get1 x a where
  get1 :: ALang t x a

instance (Avs a, Avs b) => Get1 (a,b) a where
  get1 = ArrF (return . _1) fst


class Get2 x a where
  get2 :: ALang t x a

instance (Avs a, Avs b) => Get2 (a,b) b where
  get2 = ArrF (return . _2) snd


class Set1 x y a where
  set1 :: ALang t (a,x) y 

instance (Avs a, Avs b, Avs c) => Set1 (a,b) (c,b) c where
  set1 = ArrF (\a -> return $ tuple (_1 a, _2 (_2 a))) (\(a,(_,b)) -> (a,b))

class Set2 x y a where
  set2 :: ALang t (a,x) y 

instance (Avs a, Avs b, Avs c) => Set2 (a,b) (a,c) c where
  set2 = ArrF (\a -> return $ tuple (_1 (_2 a), _1 a)) (\(a,(b,_)) -> (b,a))

over1
  :: (Avs x, Avs y, Avs a, Avs b, Get1 x a, Set1 x y b)
  => ALang t a b -> ALang t x y
over1 f = forkA >>> ATuple2 (get1 >>> f) idA >>> set1

tup2
  :: (Avs a, Avs b, Avs c)
  => (ALang t (a,b) a -> ALang t (a,b) b -> ALang t (a,b) c)
  -> ALang t (a,b) c
tup2 f = f tup2g1 tup2g2

tup2'
  :: (Avs a, Avs b, Avs c, Avs x)
  => ALang t x (a,b)
  -> (ALang t x a -> ALang t x b -> ALang t x c)
  -> ALang t x c
tup2' m f = f (m >>> tup2g1) (m >>> tup2g2)

tup22
  :: (Avs a, Avs b, Avs c, Avs d, Avs e, Avs x)
  => ALang t x ((a,b),(c,d))
  -> (((ALang t x a, ALang t x b), (ALang t x c, ALang t x d)) 
      -> ALang t x e)
  -> ALang t x e
tup22 m f =
  tup2' m $ \t1 t2 ->
  tup2' t1 $ \a b ->
  tup2' t2 $ \c d ->
  f ((a,b), (c,d))

tup2g1 :: (Avs a, Avs b) => ALang t (a,b) a
tup2g1 = ArrF (return . _1) fst

tup2g2 :: (Avs a, Avs b) => ALang t (a,b) b
tup2g2 = ArrF (return . _2) snd

fstA :: (Avs a, Avs b, Avs c) => ALang t a b -> ALang t (a,c) (b,c)
fstA = over1

over2
  :: (Avs x, Avs y, Avs a, Avs b, Get2 x a, Set2 x y b)
  => ALang t a b -> ALang t x y
over2 f = forkA >>> ATuple2 (get2 >>> f) idA >>> set2

sndA :: (Avs a, Avs b, Avs c) => ALang t b c -> ALang t (a,b) (a,c)
sndA = over2

tup3g1 :: (Avs a, Avs b, Avs c) => ALang t (a,b,c) a
tup3g1 = tup3t2 >>> tup2g1 >>> tup2g1

tup3g2 :: (Avs a, Avs b, Avs c) => ALang t (a,b,c) b
tup3g2 = tup3t2 >>> tup2g1 >>> tup2g2

tup3g3 :: (Avs a, Avs b, Avs c) => ALang t (a,b,c) c
tup3g3 = tup3t2 >>> tup2g2

tup2c1 :: (Avs a, Avs b) => a -> ALang t b (a,b)
tup2c1 a = constA a &&& idA

tup2c2 :: (Avs a, Avs b) => b -> ALang t a (a,b)
tup2c2 a = idA &&& constA a

-- Either

type Bool' = Maybe' ()

type Maybe' a = Either () a

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

eitherA
  :: (Avs a, Avs b, Avs la, Avs lb, Avs ra, Avs rb)
  => ALang t (a,la) (b,lb) -- Left case
  -> ALang t (a,ra) (b,rb) -- Right case
  -> ALang t (a, Either la ra) (b, Either lb rb)
eitherA = AEither

eitherElim
  :: (Avs a, Avs la, Avs ra, Avs b)
  => ALang t (a,la) b -- Left case
  -> ALang t (a,ra) b -- Right case
  -> ALang t (a, Either la ra) b
eitherElim ml mr =
  eitherA (ml >>> tup2c2 ()) (mr >>> tup2c2 ())
  >>> tup2g1

eitherPm
  :: (Avs a, Avs la, Avs ra, Avs b)
  => ALang t a (Either la ra)
  -> (ALang t a la -> ALang t a b) -- Left case
  -> (ALang t a ra -> ALang t a b) -- Right case
  -> ALang t a b
eitherPm fe fl fr =
  (idA &&& fe)
  >>> eitherElim (ASimulate fl) (ASimulate fr)

getLeft :: (Avs a, Avs b) => ALang t (Either a b, a) a
getLeft = flipA >>> distA >>> (tup2g2 ||| tup2g1)

getRight :: (Avs a, Avs b) => ALang t (Either a b, b) b
getRight = flipA >>> distA >>> (tup2g1 ||| tup2g2)

asLeft :: (Avs a, Avs b) => ALang t a (Either a b)
asLeft = ArrF (\a -> return $ sLeft a) Left

asRight :: (Avs a, Avs b) => ALang t b (Either a b)
asRight = ArrF (\a -> return $ sRight a) Right

onLeft :: (Avs a, Avs b, Avs c) => ALang t a b -> ALang t (Either a c) (Either b c)
onLeft f = f +++ idA

onRight :: (Avs a, Avs b, Avs c) => ALang t b c -> ALang t (Either a b) (Either a c)
onRight f = idA +++ f

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
selectA = ArrF (\a -> return $ Data.SBV.Either.either id id a)
              (\m -> case m of
                       Right a -> a
                       Left a -> a)

distA :: (Avs a, Avs b, Avs c) => ALang t (a, Either b c) (Either (a,b) (a,c)) 
distA = ArrF f1 f2
  where f1 a = return $ bimap
                          (\al -> tuple (_1 a, al))
                          (\ar -> tuple (_1 a, ar))
                          (_2 a)

        f2 (a, Left b) = Left (a,b)
        f2 (a, Right c) = Right (a,c)

undistA :: (Avs a, Avs b, Avs c) => ALang t (Either (a,b) (a,c)) (a, Either b c)
undistA = (tup2g1 ||| tup2g1) &&& (tup2g2 +++ tup2g2)

b2eA :: ALang t Bool (Either () ())
b2eA = ArrF (\a -> return (ite a (sRight su) (sLeft su)))
           (\a -> if a
                     then Right ()
                     else Left ())

e2bA :: (Avs a, Avs b) => ALang t (Either a b) Bool
e2bA = (constA False ||| constA True)

asJust :: (Avs a) => ALang t a (Maybe a)
asJust = ArrF (\a -> return $ SM.sJust a) Just

justE :: (Avs a, Avs b) => ALang t a b -> ALang t a (Maybe b)
justE m = m >>> asJust

fromJust :: (Avs a) => ALang t (a,Maybe a) a
fromJust = maybeA (tup2g2 >>> tup2c2 ()) idA >>> tup2g1

m2eA :: (Avs a) => ALang t (Maybe a) (Either () a)
m2eA = ArrF 
  (return . SM.maybe (literal (Left ())) sRight)
  (\m -> case m of
           Just a -> Right a
           Nothing -> Left ())

e2mA :: (Avs a, Avs b) => ALang t (Either a b) (Maybe b)
e2mA = ArrF 
  (return . Data.SBV.Either.either (\_ -> literal Nothing) SM.sJust)
  (\m -> case m of
           Left _ -> Nothing
           Right a -> Just a)

maybeA
  :: (Avs a, Avs b, Avs c, Avs d)
  => ALang t (a,b) (c,d) -- Just case
  -> ALang t a c -- Nothing case
  -> ALang t (a, Maybe b) (c, Maybe d)
maybeA = AMaybe

maybeElim
  :: (Avs a, Avs b, Avs c)
  => ALang t (a,b) c -- Just case
  -> ALang t a c -- Nothing case
  -> ALang t (a, Maybe b) c
maybeElim mj mn =
  maybeA (mj >>> tup2c2 ()) mn
  >>> tup2g1

maybePm
  :: (Avs a, Avs b, Avs c)
  => ALang t a (Maybe b)
  -> (ALang t a b -> ALang t a c) -- Just case
  -> ALang t a c -- Nothing case
  -> ALang t a c
maybePm fm fj fn = (idA &&& fm) >>> maybeElim (ASimulate fj) fn

bindJust
  :: (Avs a, Avs b, Avs c)
  => ALang t a (Maybe b)
  -> (ALang t a b -> ALang t a (Maybe c))
  -> ALang t a (Maybe c)
bindJust fm fj = maybePm fm fj (constA Nothing)

onJust :: (Avs a, Avs b) => ALang t a b -> ALang t (Maybe a) (Maybe b)
onJust f = tup2c1 () >>> maybeA (idA *** f) idA >>> tup2g2

-- Ints

sumA :: ALang t (Int,Int) Int
sumA = ArrF (\a -> return (_1 a + _2 a)) (\(a,b) -> a + b)

diffA :: ALang t (Int,Int) Int
diffA = over2 negateA >>> sumA

plusA :: Int -> ALang t Int Int
plusA n = idA &&& constA n >>> sumA

($+) :: (Avs a) => ALang t a Int -> ALang t a Int -> ALang t a Int
($+) m1 m2 = (m1 &&& m2) >>> sumA

($-) :: (Avs a) => ALang t a Int -> ALang t a Int -> ALang t a Int
($-) m1 m2 = (m1 &&& m2) >>> diffA

minusA :: Int -> ALang t Int Int
minusA n = idA &&& constA n >>> diffA

negateA :: ALang t Int Int
negateA = ArrF (\a -> return (-a)) (\a -> (-a))

leA :: ALang t (Int,Int) Bool
leA = ArrF (\a -> return $ _1 a .<= _2 a) (\(a,b) -> a <= b)

leE :: (Avs a) => ALang t a Int -> ALang t a Int -> ALang t a Bool
leE m1 m2 = (m1 &&& m2) >>> leA

($<=) :: (Avs a) => ALang t a Int -> ALang t a Int -> ALang t a Bool
($<=) = leE

geA :: ALang t (Int,Int) Bool
geA = ArrF (\a -> return $ _1 a .>= _2 a) (\(a,b) -> a >= b)

geE :: (Avs a) => ALang t a Int -> ALang t a Int -> ALang t a Bool
geE m1 m2 = (m1 &&& m2) >>> geA

($>=) :: (Avs a) => ALang t a Int -> ALang t a Int -> ALang t a Bool
($>=) = geE

-- Datatype construction

class (Avs d, (Avs (Content d))) => AData d where
  type Content d
  conA :: ALang t (Content d) d
  deconA :: ALang t d (Content d)

conE :: (Avs a, AData d) => ALang t a (Content d) -> ALang t a d
conE m = m >>> conA

deconE :: (Avs a, AData d) => ALang t a d -> ALang t a (Content d)
deconE m = m >>> deconA

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

returnE 
  :: (Avs a, Avs b, Avs (m b), AApplicative m) 
  => ALang t a b 
  -> ALang t a (m b)
returnE = (>>> pureA)

unitE :: (Avs a) => ALang t a ()
unitE = ca ()
