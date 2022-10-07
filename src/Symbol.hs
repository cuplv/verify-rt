{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

module Symbol where

import Data.SBV
import Data.SBV.Either
import Data.SBV.List ((.:),nil)
import Data.SBV.Maybe (sJust, sNothing)
import Data.SBV.Tuple
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Map (Map)
import qualified Data.Map as Map

class (SymVal (Rep a)) => Avs a where
  type Rep a
  toRep :: a -> Symbolic (SBV (Rep a))

type Sy a = SBV (Rep a)

instance Avs () where
  type Rep () = ()
  toRep = pure . literal

instance (Avs a, Avs b) => Avs (a,b) where
  type Rep (a,b) = (Rep a, Rep b)
  toRep (a,b) = fmap tuple $
    (,) <$> toRep a <*> toRep b

instance (Avs a, Avs b, Avs c) => Avs (a,b,c) where
  type Rep (a,b,c) = (Rep a, Rep b, Rep c)
  toRep (a,b,c) = fmap tuple $
    (,,) <$> toRep a <*> toRep b <*> toRep c

instance (Avs a, Avs b, Avs c, Avs d) => Avs (a,b,c,d) where
  type Rep (a,b,c,d) = (Rep a, Rep b, Rep c, Rep d)
  toRep (a,b,c,d) = fmap tuple $
    (,,,) <$> toRep a <*> toRep b <*> toRep c <*> toRep d

instance Avs Bool where
  type Rep Bool = Bool
  toRep = pure . literal

instance Avs Char where
  type Rep Char = Char
  toRep = pure . literal

instance (Avs a) => Avs (Maybe a) where
  type Rep (Maybe a) = Maybe (Rep a)
  toRep (Just a) = pure . sJust =<< toRep a
  toRep Nothing = pure sNothing

instance (Avs a, Avs b) => Avs (Either a b) where
  type Rep (Either a b) = Either (Rep a) (Rep b)
  toRep (Left a) = pure . sLeft =<< toRep a
  toRep (Right b) = pure . sRight =<< toRep b

instance Avs Int where
  type Rep Int = Integer
  toRep = pure . literal . fromIntegral

instance (Avs a) => Avs [a] where
  type Rep [a] = [Rep a]
  toRep (a:as) = (.:) <$> toRep a <*> toRep as
  toRep [] = pure nil

data NoRep

mkUninterpretedSort ''NoRep

newtype Some a = Some a deriving (Show,Eq,Ord)

instance Avs (Some a) where
  type Rep (Some a) = NoRep
  toRep = const forall_

data SSpec d a b
  = SSpec (Sy d -> Sy a -> Symbolic (Sy d, Sy b))

type VSpec a b = Sy a -> Symbolic (Sy b)

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

type Binr s = s -> s -> Symbolic SBool
