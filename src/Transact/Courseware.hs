module Transact.Courseware where

import ALang
import Store.Model
import Store.Model.Int (IntG)
import Transact
import qualified Transact.Int as Int
import qualified Transact.IntMap as IMap
import qualified Transact.Set as Set
import Verify (tup3Spec,trueSpec)

import Data.SBV
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
  ,IMap.G2 ()
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

noDeleteStudent :: Binr (Sy S)
noDeleteStudent s1 s2 = Set.subsetLR (_1 s1) (_1 s2)

registerStudent :: (Avs a) => Transact a G StudentId ()
registerStudent = tup3l1 $ \_ sid -> returnE (Set.insertU sid &&& ca ())

enroll :: (Avs a) => Transact a G (StudentId,CourseId) (Int,Int)
enroll = seqT
  seqWitness
    (tup3l3 $ \ctx a ->
       tup2' a $ \sid cid ->
       assertA (deconE (grantE ctx) $== sid) $
       returnE (Set.insertU (sid &&& cid) &&& a))
    (seqT
       seqWitness
       (tup3l1 $ \ctx a ->
          tup2' a $ \sid _ ->
          assertA (Set.memberE sid (stateE ctx)) $
          returnE (idU &&& a))
       (tup3l2 $ \ctx a ->
          tup2' a $ \sid _ ->
          letb (IMap.singleton (sid &&& conE (ca 1 &&& ca ()))) $ \m ->
          IMap.takeStockMulti ctx (ca 1 &&& m)))

witness :: (G, GUpd G)
witness = ((undefined,undefined,undefined), (undefined,undefined,undefined))

seqWitness = (snd Set.witness, snd IMap.witness2, snd Set.witnessP)

axioms :: Axioms
axioms =
  let (a1, f1) = IMap.axioms
      (a2, f2) = Set.axioms
      a3 = do
        s1 <- a1
        s2 <- a2
        return (s1 ++ s2)
      f3 s = f1 s >> f2 []
  in (a3,f3)
