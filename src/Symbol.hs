{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

module Symbol where

import Data.SBV
import Data.SBV.Either
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Map (Map)
import qualified Data.Map as Map

class (SymVal (Rep a)) => Avs a where
  type Rep a
  toRep :: a -> Rep a

type Sy a = SBV (Rep a)

instance Avs () where
  type Rep () = ()
  toRep = const ()

instance (Avs a, Avs b) => Avs (a,b) where
  type Rep (a,b) = (Rep a, Rep b)
  toRep (a,b) = (toRep a, toRep b)

instance (Avs a, Avs b, Avs c) => Avs (a,b,c) where
  type Rep (a,b,c) = (Rep a, Rep b, Rep c)
  toRep (a,b,c) = (toRep a, toRep b, toRep c)

instance (Avs a, Avs b, Avs c, Avs d) => Avs (a,b,c,d) where
  type Rep (a,b,c,d) = (Rep a, Rep b, Rep c, Rep d)
  toRep (a,b,c,d) = (toRep a, toRep b, toRep c, toRep d)

instance (Avs a) => Avs (Maybe a) where
  type Rep (Maybe a) = Maybe (Rep a)
  toRep (Just a) = Just (toRep a)
  toRep Nothing = Nothing

instance (Avs a, Avs b) => Avs (Either a b) where
  type Rep (Either a b) = Either (Rep a) (Rep b)
  toRep (Left a) = Left (toRep a)
  toRep (Right b) = Right (toRep b)

instance Avs Int where
  type Rep Int = Integer
  toRep = fromIntegral

instance (Ord (Rep k), Avs k) => Avs (Map k w) where
  type Rep (Map k w) = [Rep k]
  toRep = map toRep . Map.keys

instance (Avs a) => Avs [a] where
  type Rep [a] = [Rep a]
  toRep = map toRep

instance Avs Char where
  type Rep Char = Char
  toRep = id

data SSpec d a b
  = SSpec (Sy d -> Sy a -> Symbolic (Sy d, Sy b))

data VSpec a b
  = VSpec (Sy a -> Symbolic (Sy b))

su = literal ()

eitherM
  :: (Monad m, SymVal a, SymVal b, SymVal c)
  => (SBV a -> m (SBV c))
  -> (SBV b -> m (SBV c))
  -> SEither a b
  -> m (SBV c)
eitherM ml mr v = do
  cl <- ml (fromLeft v)
  cr <- mr (fromRight v)
  return $ Data.SBV.Either.either (const cl) (const cr) v

bimapM
  :: (Monad m, SymVal a1, SymVal a2, SymVal b1, SymVal b2)
  => (SBV a1 -> m (SBV b1))
  -> (SBV a2 -> m (SBV b2))
  -> SEither a1 a2
  -> m (SEither b1 b2)
bimapM ml mr = eitherM (\a -> sLeft <$> ml a) (\a -> sRight <$> mr a)

data TSpec d a b
  = TSpec { tSpec :: Sy d -> Sy a -> Sy d -> Sy b -> Symbolic SBool
          }

instance (Avs d, Avs a, Avs b) => Semigroup (TSpec d a b) where
  TSpec m1 <> TSpec m2 = TSpec
    (\a d b d' -> do r1 <- m1 a d b d' 
                     r2 <- m2 a d b d'
                     return (r1 .&& r2))

instance (Avs d, Avs a, Avs b) => Monoid (TSpec d a b) where
  mempty = TSpec (\_ _ _ _ -> return sTrue)

invarS :: (Avs d, Avs a, Avs b) => (Sy d -> Symbolic SBool) -> TSpec d a b
invarS f = TSpec (\d _ d' _ -> do r1 <- f d
                                  r2 <- f d'
                                  return $ r1 .=> r2)

prePostS :: (Avs d, Avs a, Avs b) => (Sy d -> Sy d -> Symbolic SBool) -> TSpec d a b
prePostS f = TSpec (\d _ d' _ -> f d d')
