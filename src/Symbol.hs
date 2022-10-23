{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

module Symbol where

import Symbol.Axioms (loadAxiomsDhall)

import Data.SBV
import qualified Data.SBV.Either as SE
import qualified Data.SBV.List as SL
import qualified Data.SBV.Maybe as SM
import Data.SBV.Tuple
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Map (Map)
import qualified Data.Map as Map

class (SymVal (Rep a)) => Avs a where
  type Rep a

class (Avs a) => Avc a where
  toRep :: a -> Symbolic (SBV (Rep a))
  repc :: a -> SBV (Rep a) -> SBool

type Sy a = SBV (Rep a)

instance Avs () where
  type Rep () = ()

instance Avc () where
  toRep = pure . literal
  repc = (.==) . literal

instance (Avs a, Avs b) => Avs (a,b) where
  type Rep (a,b) = (Rep a, Rep b)

instance (Avc a, Avc b) => Avc (a,b) where
  toRep (a,b) = fmap tuple $
    (,) <$> toRep a <*> toRep b
  repc (a,b) z = repc a (_1 z) .&& repc b (_2 z)

instance (Avs a, Avs b, Avs c) => Avs (a,b,c) where
  type Rep (a,b,c) = (Rep a, Rep b, Rep c)

instance (Avc a, Avc b, Avc c) => Avc (a,b,c) where
  toRep (a,b,c) = fmap tuple $
    (,,) <$> toRep a <*> toRep b <*> toRep c
  repc (a,b,c) z = repc a (_1 z) .&& repc b (_2 z) .&& repc c (_3 z)

instance (Avs a, Avs b, Avs c, Avs d) => Avs (a,b,c,d) where
  type Rep (a,b,c,d) = (Rep a, Rep b, Rep c, Rep d)

instance (Avc a, Avc b, Avc c, Avc d) => Avc (a,b,c,d) where
  toRep (a,b,c,d) = fmap tuple $
    (,,,) <$> toRep a <*> toRep b <*> toRep c <*> toRep d
  repc (a,b,c,d) z =
    repc a (_1 z)
    .&& repc b (_2 z)
    .&& repc c (_3 z)
    .&& repc d (_4 z)

instance Avs Bool where
  type Rep Bool = Bool

instance Avc Bool where
  toRep = pure . literal
  repc = (.==) . literal

instance Avs Char where
  type Rep Char = Char

instance Avc Char where
  toRep = pure . literal
  repc = (.==) . literal

instance (Avs a) => Avs (Maybe a) where
  type Rep (Maybe a) = Maybe (Rep a)

instance (Avc a) => Avc (Maybe a) where
  toRep (Just a) = pure . SM.sJust =<< toRep a
  toRep Nothing = pure SM.sNothing
  repc (Just a) = SM.maybe sFalse (repc a)
  repc Nothing = SM.maybe sTrue (const sFalse)

instance (Avs a, Avs b) => Avs (Either a b) where
  type Rep (Either a b) = Either (Rep a) (Rep b)

instance (Avc a, Avc b) => Avc (Either a b) where
  toRep (Left a) = pure . SE.sLeft =<< toRep a
  toRep (Right b) = pure . SE.sRight =<< toRep b
  repc (Left a) = SE.either (repc a) (const sFalse)
  repc (Right b) = SE.either (const sFalse) (repc b)

instance Avs Int where
  type Rep Int = Integer

instance Avc Int where
  toRep = pure . literal . fromIntegral
  repc = (.==) . literal . fromIntegral

instance (Avs a) => Avs [a] where
  type Rep [a] = [Rep a]

instance (Avc a) => Avc [a] where
  toRep (a:as) = (SL..:) <$> toRep a <*> toRep as
  toRep [] = pure SL.nil
  repc (a:as) z = let (za,zs) = SL.uncons z
                  in repc a za .&& repc as zs

data NoRep

mkUninterpretedSort ''NoRep

newtype Some a = Some a deriving (Show,Eq,Ord)

instance Avs (Some a) where
  type Rep (Some a) = NoRep

instance Avc (Some a) where
  toRep = const forall_
  repc _ _ = sTrue

data SSpec d a b
  = SSpec (Sy d -> Sy a -> Symbolic (Sy d, Sy b))

type FSpec a b = Sy a -> Symbolic (Sy b)

type PSpec a b = Sy a -> Sy b -> Symbolic SBool

su = literal ()

eitherM
  :: (Monad m, SymVal a, SymVal b, SymVal c)
  => (SBV a -> m (SBV c))
  -> (SBV b -> m (SBV c))
  -> SEither a b
  -> m (SBV c)
eitherM ml mr v = do
  cl <- ml (SE.fromLeft v)
  cr <- mr (SE.fromRight v)
  return $ SE.either (const cl) (const cr) v

bimapM
  :: (Monad m, SymVal a1, SymVal a2, SymVal b1, SymVal b2)
  => (SBV a1 -> m (SBV b1))
  -> (SBV a2 -> m (SBV b2))
  -> SEither a1 a2
  -> m (SEither b1 b2)
bimapM ml mr = eitherM (\a -> SE.sLeft <$> ml a) (\a -> SE.sRight <$> mr a)

type Binr s = s -> s -> Symbolic SBool

type Axioms = (IO [String], [String] -> Symbolic ())

mkAxiomLoader :: String -> ([String] -> Symbolic ()) -> Axioms
mkAxiomLoader s f = (loadAxiomsDhall s, f)

loadAxioms :: Axioms -> IO [String]
loadAxioms = fst

applyAxioms :: Axioms -> [String] -> Symbolic ()
applyAxioms = snd
