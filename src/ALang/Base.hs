{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}

module ALang.Base where

import ALang.Construct
import Symbol

import Data.SBV
import Data.SBV.Either
import Data.SBV.Tuple

(<<<) :: (Avs a, Avs b, Avs c) => ALang t b c -> ALang t a b -> ALang t a c
(<<<) = PipeRL

(>>>) :: (Avs a, Avs b, Avs c) => ALang t a b -> ALang t b c -> ALang t a c
(>>>) = flip PipeRL

idA :: (Avs a) => ALang t a a
idA = Arr return id

funA :: (Avs a, Avs b) => (a -> b) -> ALang t a b
funA  = Arr (const forall_)

constA :: (Avs a, Avs b) => b -> ALang t a b
constA b = Arr (const . return . literal $ toRep b) (const b)

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

over2
  :: (Avs x, Avs y, Avs a, Avs b, Get2 x a, Set2 x y b)
  => ALang t a b -> ALang t x y
over2 f = forkA >>> ATimes (get2 >>> f) idA >>> set2
