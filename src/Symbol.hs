{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeFamilies #-}

module Symbol where

import Data.SBV
import Data.SBV.Either

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

instance (Avs a, Avs b) => Avs (Either a b) where
  type Rep (Either a b) = Either (Rep a) (Rep b)
  toRep (Left a) = Left (toRep a)
  toRep (Right b) = Right (toRep b)

instance Avs Int where
  type Rep Int = Integer
  toRep n = fromIntegral n

instance Avs [a] where
  type Rep [a] = ()
  toRep = const ()

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
  = TSpec { inputSpec :: Sy a -> SBV Bool
          , mainSpec :: Sy d -> Sy a -> Sy d -> Sy b -> SBV Bool
          }

instance (Avs d, Avs a, Avs b) => Semigroup (TSpec d a b) where
  TSpec i1 m1 <> TSpec i2 m2 = TSpec
    (\a -> i1 a .&& i2 a)
    (\a d b d' -> m1 a d b d' .&& m2 a d b d')

instance (Avs d, Avs a, Avs b) => Monoid (TSpec d a b) where
  mempty = TSpec (\_ -> sTrue) (\_ _ _ _ -> sTrue)

inputS :: (Avs d, Avs a, Avs b) => (Sy a -> SBV Bool) -> TSpec d a b
inputS f = TSpec f (\_ _ _ _ -> sTrue)

invarS :: (Avs d, Avs a, Avs b) => (Sy d -> Sy d -> SBV Bool) -> TSpec d a b
invarS f = TSpec (\_ -> sTrue) (\d _ d' _ -> f d d')
