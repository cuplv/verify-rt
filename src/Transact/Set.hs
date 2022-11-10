{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

module Transact.Set where

import ALang
import ALang.Construct
import Store.Model
import Transact

import Data.SBV
import qualified Data.SBV.Set as SSet
import Data.SBV.Tuple
import Data.Set (Set)
import qualified Data.Set as Set

subsetLR :: Sy (Set Int) -> Sy (Set Int) -> Symbolic SBool
subsetLR s1 s2 = return $ SSet.isSubsetOf s1 s2

subsetLR' :: Sy (Set Int, Set Int) -> Sy (Set Int, Set Int) -> Symbolic SBool
subsetLR' s1 s2 = return $
  SSet.isSubsetOf (_1 s1) (_2 s1)
  .=> SSet.isSubsetOf (_1 s2) (_2 s2)

emptyE
  :: (Avs a, Avs b, Ord (Rep b))
  => ALang t a (Set b)
emptyE = arrC SSet.empty Set.empty

singletonE
  :: (Avs a, Avs b, Ord (Rep b))
  => ALang t a b -> ALang t a (Set b)
singletonE = eform $ ArrF
  (pure . SSet.singleton)
  Set.singleton

insertE
  :: (Avs a, Avs b, Ord b, Ord (Rep b))
  => ALang t a b -> ALang t a (Set b) -> ALang t a (Set b)
insertE = eform2 $ ArrF
  (\a -> pure $ SSet.insert (_1 a) (_2 a))
  (\(a,s) -> Set.insert a s)

deleteE
  :: (Avs a, Avs b, Ord b, Ord (Rep b))
  => ALang t a b -> ALang t a (Set b) -> ALang t a (Set b)
deleteE = eform2 $ ArrF
  (\a -> pure $ SSet.delete (_1 a) (_2 a))
  (\(a,s) -> Set.delete a s)

unionE
  :: (Avs a, Avs b, Ord b, Ord (Rep b))
  => ALang t a (Set b)
  -> ALang t a (Set b)
  -> ALang t a (Set b)
unionE = eform2 $ ArrF
  (\a -> pure $ SSet.union (_1 a) (_2 a))
  (\(a,b) -> Set.union a b)

differenceE
  :: (Avs a, Avs b, Ord b, Ord (Rep b))
  => ALang t a (Set b)
  -> ALang t a (Set b)
  -> ALang t a (Set b)
differenceE = eform2 $ ArrF
  (\a -> pure $ SSet.difference (_1 a) (_2 a))
  (\(a,b) -> Set.difference a b)

intersectionE
  :: (Avs a, Avs b, Ord b, Ord (Rep b))
  => ALang t a (Set b)
  -> ALang t a (Set b)
  -> ALang t a (Set b)
intersectionE = eform2 $ ArrF
  (\a -> pure $ SSet.intersection (_1 a) (_2 a))
  (\(a,b) -> Set.intersection a b)

memberE
  :: (Avs a, Avs b, Ord b, Ord (Rep b))
  => ALang t a b
  -> ALang t a (Set b)
  -> ALang t a Bool
memberE = eform2 $ ArrF
  (\a -> pure $ SSet.member (_1 a) (_2 a))
  (\(a,b) -> Set.member a b)

data SetUpd a
  = SetInsert a
  | SetDelete a
  | SetNoOp
  deriving (Show,Eq,Ord)

-- data SetUpd a
--   = SetUpd { setUpdInsert :: Set a
--            , setUpdDelete :: Set a
--            }
--   deriving (Show)

instance (Avs a) => Avs (SetUpd a) where
  -- type Rep (SetUpd a) = (RCSet (Rep a), RCSet (Rep a))
  type Rep (SetUpd a) = Maybe (Rep a, Bool)

instance (Avs a, Ord (Rep a)) => AData (SetUpd a) where
  type Content (SetUpd a) = Maybe (a,Bool)
  conA = ArrF return (\m -> case m of
                              Just (a,True) -> SetInsert a
                              Just (a,False) -> SetDelete a
                              Nothing -> SetNoOp)
  deconA = ArrF return (\u -> case u of
                                SetInsert a -> Just (a,True)
                                SetDelete a -> Just (a,False)
                                SetNoOp -> Nothing)

insertU
  :: (Avs a, Avs b, Ord b, Ord (Rep b))
  => ALang t a b -> ALang t a (SetUpd b)
insertU e = conE (justE (e &&& ca True))

deleteU
  :: (Avs a, Avs b, Ord b, Ord (Rep b))
  => ALang t a b -> ALang t a (SetUpd b)
deleteU e = conE (justE (e &&& ca False))

instance (Avs a, Ord a, Ord (Rep a)) => Update (SetUpd a) where
  type UState (SetUpd a) = Set a
  mkIdU = conE nothingE
  seqU _ = unEform2 $ \u1 u2 ->
    iteS (isNothingE (deconE u1)) u2 u1
  applyU _ = unEform2 $ \u s ->
    maybePm 
      (deconE u)
      (\a -> tup2' a $ \e b -> iteS b (insertE e s) (deleteE e s))
      s

{-| A multi-level lock, providing shared-insert, shared-delete, and
  exclusive modes.

  When only 'canInsert' is true, you are taking part in shared-insert.

  When only 'canDelete' is true, you are taking part in shared-delete.

  When both are true, you have the exclusive lock.

  When both are false, someone else has the exclusive lock.
-}
data MultiG a
  = MultiG { allowInsert :: Bool
           , allowDelete :: Bool
           }
  deriving (Show,Eq,Ord)

witness :: (MultiG Int, SetUpd Int)
witness = (undefined, undefined)

witness2 :: ((MultiG Int, MultiG Int), (SetUpd Int, SetUpd Int))
witness2 = ((undefined, undefined), (undefined, undefined))

witnessP :: (PartG Int Int, SetUpd (Int,Int))
witnessP = (undefined,undefined)

instance Avs (MultiG a) where
  type Rep (MultiG a) = (Bool, Bool)

instance Avc (MultiG a) where
  toRep (MultiG a b) = pure $ tuple (literal a, literal b)
  repc (MultiG a b) s = (literal a .== _1 s) .&& (literal b .== _2 s)

instance AData (MultiG a) where
  type Content (MultiG a) = (Bool, Bool)
  conA = ArrF return (\(a,b) -> MultiG a b)
  deconA = ArrF return (\(MultiG a b) -> (a,b))

instance (Avs a, Ord a, Ord (Rep a)) => Grant (MultiG a) where
  type GUpd (MultiG a) = SetUpd a
  -- If we can insert, then the remote context cannot delete, and so
  -- the local state is a subset of the remote state.
  --
  -- If we can delete, then the remote context cannot insert, and so
  -- the remote state is a subset of the local state.
  --
  -- If we can do both, then the remote context can do nothing, and
  -- local state is equal to remote state (the other cases already
  -- imply this).
  readG _ g s1 s2 = return $
    (_1 g .=> s1 `SSet.isSubsetOf` s2)
    .&& (_2 g .=> s2 `SSet.isSubsetOf` s1)
  writeG _ g s1 s2 = return $
    (sNot (_1 g) .=> s2 `SSet.isSubsetOf` s1)
    .&& (sNot (_2 g) .=> s1 `SSet.isSubsetOf` s2)
  useG _ = undefined

canInsert :: (Avs a, Avs b) => ALang t a (MultiG b) -> ALang t a Bool
canInsert g = tup2' (deconE g) $ \i _ -> i

canDelete :: (Avs a, Avs b) => ALang t a (MultiG b) -> ALang t a Bool
canDelete g = tup2' (deconE g) $ \_ d -> d

canBoth :: (Avs a, Avs b) => ALang t a (MultiG b) -> ALang t a Bool
canBoth g = canInsert g $/\ canDelete g

assertMember
  :: (Avs a, Avs b, Ord b, Ord (Rep b))
  => Transact a (MultiG b) b b
assertMember ctx val =
  -- If we canInsert, then no-one else canDelete
  assertA (canInsert (grantE ctx)) $
  assertA (memberE val (stateE ctx)) $
  returnE (idU &&& val)

assertNotMember
  :: (Avs a, Avs b, Ord b, Ord (Rep b))
  => Transact a (MultiG b) b b
assertNotMember ctx val =
  -- If we canDelete, then no-one else canInsert
  assertA (canDelete (grantE ctx)) $
  assertA (notE $ memberE val (stateE ctx)) $
  returnE (idU &&& val)

insertLeft
  :: (Avs a)
  => Transact a (MultiG Int, MultiG Int) Int ()
insertLeft = seqT
  (undefined, undefined)
  (tup2l2 assertMember)
  (tup2l1 $ \ctx val ->
     assertA (canInsert (grantE ctx)) $
     returnE (insertU val &&& ca ()))

badInsertLeft
  :: (Avs a, Avs b, Ord b, Ord (Rep b))
  => Transact a (MultiG b, MultiG b) b ()
badInsertLeft = tup2l1 $ \ctx val ->
  assertA (canInsert (grantE ctx)) $
  returnE (insertU val &&& ca ())

insertRight
  :: (Avs a, Avs b, Ord b, Ord (Rep b))
  => Transact a (MultiG b, MultiG b) b ()
insertRight = tup2l2 $ \ctx val ->
  assertA (canInsert (grantE ctx)) $
  returnE (insertU val &&& ca ())

capFailInsertRight
  :: (Avs a, Avs b, Ord b, Ord (Rep b))
  => Transact a (MultiG b, MultiG b) b ()
capFailInsertRight = tup2l2 $ \ctx val ->
  returnE (insertU val &&& ca ())

deleteLeft
  :: (Avs a, Avs b, Ord b, Ord (Rep b))
  => Transact a (MultiG b, MultiG b) b ()
deleteLeft = tup2l1 $ \ctx val ->
  assertA (canDelete (grantE ctx)) $
  returnE (deleteU val &&& ca ())

capFailDeleteLeft
  :: (Avs a, Avs b, Ord b, Ord (Rep b))
  => Transact a (MultiG b, MultiG b) b ()
capFailDeleteLeft = tup2l1 $ \ctx val ->
  returnE (deleteU val &&& ca ())

deleteRight
  :: (Avs a)
  => Transact a (MultiG Int, MultiG Int) Int ()
deleteRight = seqT
  (undefined, undefined)
  (tup2l1 assertNotMember)
  (tup2l2 $ \ctx val ->
     assertA (canDelete (grantE ctx)) $
     returnE (deleteU val &&& ca ()))

badDeleteRight
  :: (Avs a, Avs b, Ord b, Ord (Rep b))
  => Transact a (MultiG b, MultiG b) b Bool
badDeleteRight = tup2l2 $ \ctx val ->
  assertA (canDelete (grantE ctx)) $
  returnE (deleteU val &&& ca True)

data PartG a b = PartG a deriving (Show,Eq,Ord)

instance (Avs a) => Avs (PartG a b) where
  type Rep (PartG a b) = Rep a

instance (Avc a) => Avc (PartG a b) where
  toRep (PartG a) = toRep a
  repc (PartG a) s = error "Can't implement repc for PartG actually."

instance (Avs a) => AData (PartG a b) where
  type Content (PartG a b) = a
  conA = ArrF return PartG
  deconA = ArrF return (\(PartG a) -> a)

instance Grant (PartG Int Int) where
  type GUpd (PartG Int Int) = SetUpd (Int,Int)
  readG _ g s1 s2 = do
    return $ partLocked g s1 s2
  writeG _ g s1 s2 = do
    v <- forall_
    constrain $ _1 v ./= g
    return $ SSet.member v s1 .<=> SSet.member v s2
  useG _ = undefined

partLocked :: SInteger -> SSet (Integer,Integer) -> SSet (Integer,Integer) -> SBool
partLocked = uninterpret $ "partLocked"

partSubset :: SSet Integer -> SSet (Integer,Integer) -> SBool
partSubset = uninterpret $ "partSubset"

-- First int is partition, second is size
partHasSize :: SInteger -> SSet (Integer,Integer) -> SInteger -> SBool
partHasSize = uninterpret $ "partHasSize"

test :: IO ThmResult
test = do
  ss <- loadAxioms axioms
  proveWith (z3 {verbose = True}) $ do
    applyAxioms axioms ss
    s1 <- forall "s1"
    s2 <- forall "s2"
    s3 <- forall "s3"
    s4 <- forall "s4"
    constrain $ sNot (SSet.member (tuple (1 :: SInteger,3 :: SInteger)) s1)
    constrain =<< readG (undefined :: PartG Int Int) 1 s1 s2
    let p1 = sNot (SSet.member (tuple (1 :: SInteger,3 :: SInteger)) s2)
    let p2 = partSubset s3 SSet.empty
    let p3 = partSubset (SSet.singleton 1) (SSet.singleton $ tuple (1,1))
    let p4 = sNot $ partSubset (SSet.singleton 2) (SSet.singleton $ tuple (1,2))
    let p5 = partSubset (SSet.singleton 1) s4
             .=> sNot (SSet.member (tuple (2,2)) s4)
    let p6 = (partHasSize 3 s1 99 .&& sNot (SSet.member (tuple (1,3)) s1))
             .=> partHasSize 3 (SSet.insert (tuple (1,3)) s1) 100
    let p7 = (partHasSize 3 s1 99 .&& SSet.member (tuple (1,3)) s1)
             .=> partHasSize 3 (SSet.delete (tuple (1,3)) s1) 98
    return $ p1 .&& p2 .&& p3 .&& p4 .&& p5 .&& p6 .&& p7

addAxioms' :: [String] -> Symbolic ()
addAxioms' ss = do
  addAxiom "PartSetAxioms" ss
  i <- forall_
  s1 <- forall_
  s2 <- forall_
  s3 <- forall_
  constrain $ partLocked i s1 s2 .== partLocked i s1 s2
  constrain $ partSubset s3 s2 .== partSubset s3 s2
  constrain $ partHasSize i s1 i .== partHasSize i s1 i

axioms :: Axioms
axioms = mkAxiomLoader "PartSet" addAxioms'
