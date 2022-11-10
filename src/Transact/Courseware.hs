module Transact.Courseware where

import ALang
import Store.Model
import Store.Model.Int (IntG)
import Transact
import qualified Transact.Int as Int
import qualified Symbol.IntMap as SMap
import qualified Transact.IntMap as IMap
import qualified Transact.Set as Set
import Verify (tup3Spec,trueSpec)

import Data.SBV
import qualified Data.SBV.Maybe as SMaybe
import qualified Data.SBV.Set as SSet
import Data.SBV.Tuple
import Data.Set (Set)

type StudentId = Int
type CourseId = Int
type S = 
   -- Existing students
  (Set StudentId
   -- Existing courses and capacities
  ,IMap.Map'
   -- Enrollments
  ,Set (StudentId, CourseId)
  )

type G =
   -- Changes to student table are not coordinated (but are limited by
   -- app correctness property!)
  (UnCoord (Set.SetUpd StudentId)
   -- Per-course escrow allocations
  ,IMap.G1 ()
   -- Per-student partition locks
  ,Set.PartG StudentId CourseId
  )

coursewareSpec :: Binr (Sy S)
coursewareSpec s1 s2 = do 
  r1 <- tup3Spec
          (Set.subsetLR
          ,IMap.nonNegative
          ,trueSpec)
          s1 s2
  let r2 = Set.partSubset (_1 s1) (_3 s1) .=> Set.partSubset (_1 s2) (_3 s2)
  return $ r1 .&& r2

enrollDomain :: Binr (Sy S)
enrollDomain s1 s2 = do
  r1 <- noDeleteStudent s1 s2
  let r2 = Set.partSubset (_1 s1) (_3 s1) .=> Set.partSubset (_1 s2) (_3 s2)
  return $ r1 .&& r2

capacityValue :: Binr (Sy S)
capacityValue s1 s2 = IMap.nonNegative (_2 s1) (_2 s2)
-- capacityValue s1 s2 = do
--   (k,v1) <- SMap.anyEntry (_2 s1)
--   mv2 <- SMap.lookup k (_2 s2)
--   return $ SMaybe.maybe
--     sTrue
--     (\v2 -> ((partMapMatch 30 (_3 s1) (_2 s1) .&& v1 .>= 0) )
--              .=> (partMapMatch 30 (_3 s2) (_2 s2) .&& (v2 .>= 0)))
--     mv2

capacityMatch :: Binr (Sy S)
capacityMatch s1 s2 = do
  return $ partMapMatch 30 (_3 s1) (_2 s1) .=> partMapMatch 30 (_3 s2) (_2 s2)

noDeleteStudent :: Binr (Sy S)
noDeleteStudent s1 s2 = Set.subsetLR (_1 s1) (_1 s2)

registerStudent :: (Avs a) => Transact a G StudentId ()
registerStudent = tup3l1 $ \_ sid -> returnE (Set.insertU sid &&& ca ())

enroll :: (Avs a) => Transact a G (StudentId,CourseId) (Int)
-- enroll = tup3l2 $ \ctx a ->
--           tup2' a $ \sid _ ->
--           letb (IMap.singleton (sid &&& conE (ca 1 &&& ca ()))) $ \m ->
--           -- Subtract that map from the course capacity map (checking
--           -- that there is capacity to do so)
--           IMap.takeStockMulti ctx (ca 1 &&& m)
enroll = seqT
  seqWitness
    -- Add entry to enrollment table
    (tup3l3 $ \ctx a ->
       tup2' a $ \sid _ ->
       -- Check that we have student's enrollment lock
       assertA (deconE (grantE ctx) $== sid) $
       -- Check that student is not already enrolled in this course.
       assertA (notE (Set.memberE a (stateE ctx))) $
       -- Insert, and also pass the (sid,cid) along
       returnE (Set.insertU a &&& a))
    (seqT
       seqWitness
       -- Ensure that student exists
       (tup3l1 $ \ctx a ->
          tup2' a $ \sid _ ->
          assertA (Set.memberE sid (stateE ctx)) $
          returnE (idU &&& a))
       -- Decrement course capacity
       (tup3l2 $ \ctx a ->
          tup2' a $ \_ cid ->
          -- Construct a singleton map { cid -> 1 }
          letb (IMap.singleton (cid &&& conE (ca 1 &&& ca ()))) $ \m ->
          -- Subtract that map from the course capacity map (checking
          -- that there is capacity to do so)
          -- IMap.takeStockMulti ctx (ca 1 &&& m)
          requireE (deconE (grantE ctx)) $ \k ->
          assertA (k $== cid) $
          IMap.takeStock ctx (ca 1)
          ))

witness :: (G, GUpd G)
witness = ((undefined,undefined,undefined), (undefined,undefined,undefined))

seqWitness = (snd Set.witness, snd IMap.witness2, snd Set.witnessP)

partMapMatch :: SInteger -> SSet (Integer,Integer) -> Sy IMap.Map' -> SBool
partMapMatch = uninterpret $ "partMapMatch"

addAxioms' :: [String] -> Symbolic ()
addAxioms' ss = do
  addAxiom "PartSetIntMapAxioms" ss
  i <- forall_
  s <- forall_
  m <- forall_
  constrain $ partMapMatch i s m .== partMapMatch i s m
  return ()

axiomsPI :: Axioms
axiomsPI = mkAxiomLoader "PartSetIntMap" addAxioms'

axioms :: Axioms
axioms =
  let (a1, f1) = IMap.axioms
      (a2, f2) = Set.axioms
      (a3, f3) = axiomsPI
      a4 = do
        s1 <- a1
        s2 <- a2
        s3 <- a3
        return (s1 ++ s2 ++ s3)
      f4 s = f1 s >> f2 [] >> f3 []
  in (a4,f4)

test :: IO ThmResult
test = do
  ss <- loadAxioms axioms
  proveWith (z3 {verbose = True}) $ do
    applyAxioms axioms ss
    s1 <- forall "s1"
    m1 <- forall "m1"
    constrain $ partMapMatch 30 s1 m1
    constrain $ SMap.hasVal 6 2 m1
    let r1 = Set.partHasSize 6 s1 28
    
    s2 <- forall "s2"
    m2 <- forall "m2"
    m2' <- forall_
    constrain $ partMapMatch 30 s2 m2
    constrain $ sNot (SSet.member (tuple (2,1)) s2)
    mm <- forall_
    constrain $ SMap.singleton 1 (-1) mm
    constrain $ SMap.update (SMap.mapModify mm) m2 m2'
    let s2' = SSet.insert (tuple (2,1)) s2
        r2 = partMapMatch 30 s2' m2'
        
    s3 <- forall "s3"
    m3 <- forall "m3"
    m3' <- forall_
    constrain $ partMapMatch 30 s3 m3
    constrain $ SSet.member (tuple (2,1)) s3
    constrain $ SMap.update (SMap.modify 1 1) m3 m3'
    let s3' = SSet.delete (tuple (2,1)) s3
        r3 = partMapMatch 30 s3' m3'

    return $ r1 .&& r2 .&& r3
