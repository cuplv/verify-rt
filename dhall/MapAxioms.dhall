let lib = ./lib.dhall in

\(i : lib.MapInst) ->

let mkfun = lib.mkfun i

let empty = mkfun "empty"
let singleton = mkfun "singleton"
let member = mkfun "member"
let hasVal = mkfun "hasVal"
let match = mkfun "match"
let valUpdate = mkfun "valUpdate"
let update = mkfun "update"
let identity = mkfun "identity"
let insert = mkfun "insert"
let modify = mkfun "modify"
let delete = mkfun "delete"
let seq = mkfun "seq"

let qk1 = "(k1 ${i.key})"
let qk2 = "(k2 ${i.key})"
let qv1 = "(v1 ${i.val})"
let qv2 = "(v2 ${i.val})"
let qm1 = "(m1 ${i.map})"
let qm2 = "(m2 ${i.map})"
let qm3 = "(m3 ${i.map})"
let qu1 = "(u1 ${i.upd})"
let qu2 = "(u2 ${i.upd})"
let qf1 = "(f1 ${i.valUpd})"
let qf2 = "(f2 ${i.valUpd})"

let baseAxioms =

-- -- All types are inhabited
-- ''
-- (assert (exists (${qk1}) true))
-- (assert (exists (${qv1}) true))
-- (assert (exists (${qm1}) true))
-- (assert (exists (${qu1}) true))
-- (assert (exists (${qf1}) true))
-- ''

-- Define empty map, as no members
''
(assert (forall (${qk1} ${qm1})
  (=>
    (${empty} m1)
    (not (${member} k1 m1)))))
''

-- All empty maps are equivalent
++ ''
(assert (forall (${qm1} ${qm2})
  (=>
    (and (${empty} m1) (${empty} m2))
    (= m1 m2))))
''

-- -- Define singleton map
-- (
-- let m = "(${singleton} k1 v1)"
-- in ''
-- (assert (forall (${qk1} ${qv1})
--   (and
--     (${hasVal} k1 v1 ${m})
--     (${member} k1 ${m}))))

-- (assert (forall (${qk1} ${qk2} ${qv1})
--   (=>
--     (distinct k1 k2)
--     (not (${member} k2 ${m})))))
-- '')

-- Singleton v2
++ ''
(assert (forall (${qk1} ${qv1} ${qm1})
  (=>
    (${singleton} k1 v1 m1)
    (${hasVal} k1 v1 m1))))

(assert (forall (${qk1} ${qk2} ${qv1} ${qm1})
  (=>
    (and (distinct k1 k2) (${singleton} k1 v1 m1))
    (not (${member} k2 m1)))))

(assert (forall (${qk1} ${qv1} ${qm1} ${qm2})
  (=>
    (and (${singleton} k1 v1 m1) (${singleton} k1 v1 m2))
    (= m1 m2))))
''

-- Define match
-- (This one looks dicey, might want to split into simpler statements)
++ ''
(assert (forall (${qk1} ${qm1} ${qm2})
  (= (${match} k1 m1 m2)
    (and
      (forall (${qv1}) (= (${hasVal} k1 v1 m1) (${hasVal} k1 v1 m2)))
      (= (${member} k1 m1) (${member} k1 m2))))))
''

-- -- There are at least 2 values
-- ++ ''
-- (assert (forall (${qk1} ${qm1})
--   (exists (${qv1})
--     (not (${hasVal} k1 v1 m1)))))
-- (assert (not (forall (${qk1} ${qv1} ${qm1}) (${hasVal} k1 v1 m1))))
-- ''

-- Equivalence from matching on all keys
++ ''
(assert (forall (${qm1} ${qm2})
  (= (= m1 m2)
     (forall (${qk1}) (${match} k1 m1 m2)))))
''

-- Matching is reflexive (same as previous axiom?)
++ ''
(assert (forall (${qk1} ${qm1})
  (${match} k1 m1 m1)))
''

-- Matching is symmetric
++ ''
(assert (forall (${qk1} ${qm1} ${qm2})
  (= (${match} k1 m1 m2) (${match} k1 m2 m1))))
''

-- Matching is transitive
++ ''
(assert (forall (${qk1} ${qm1} ${qm2} ${qm3})
  (=>
    (and (${match} k1 m1 m2) (${match} k1 m2 m3))
    (${match} k1 m1 m3))))
''

-- hasVal implies member
++ ''
(assert (forall (${qk1} ${qv1} ${qm1})
  (=> (${hasVal} k1 v1 m1) (${member} k1 m1))))
''

-- member implies exists hasVal
++ ''
(assert (forall (${qk1} ${qm1})
  (=>
    (${member} k1 m1)
    (exists (${qv1}) (${hasVal} k1 v1 m1)))))
''

-- hasVal is unique
++ ''
(assert (forall (${qk1} ${qv1} ${qv2} ${qm1})
  (=>
    (and (${hasVal} k1 v1 m1) (${hasVal} k1 v2 m1))
    (= v1 v2))))
''

-- Define identity update
++ ''
(assert (forall (${qm1} ${qm2})
  (=
    (${update} ${identity} m1 m2)
    (= m1 m2))))
''

-- -- Define insert update
-- ++ ''
-- (assert (forall (${qk1} ${qv1} ${qm1} ${qm2})
--   (=
--     (${update} (${insert} k1 v1) m1 m2)
--     (and
--       (${hasVal} k1 v1 m2)
--       (forall (${qk2})
--         (or (= k1 k2) (${match} k2 m1 m2)))))))
-- ''

-- Insert v2
++ ''
(assert (forall (${qk1} ${qv1} ${qm1} ${qm2})
  (=>
    (${update} (${insert} k1 v1) m1 m2)
    (${hasVal} k1 v1 m2))))

(assert (forall (${qk1} ${qk2} ${qv1} ${qm1} ${qm2})
  (=>
    (and (distinct k1 k2) (${update} (${insert} k1 v1) m1 m2))
    (${match} k2 m1 m2))))
''

-- -- Define delete update
-- ++ ''
-- (assert (forall (${qk1} ${qm1} ${qm2})
--   (=
--     (${update} (${delete} k1) m1 m2)
--     (and
--       (not (${member} k1 m2))
--       (forall (${qk2})
--         (or (= k1 k2) (${match} k2 m1 m2)))))))
-- (assert (forall (${qk1} ${qm1})
--   (=
--     (${update} (${delete} k1) m1 m1)
--     (not (${member} k1 m1)))))
-- ''

-- Delete v2
++ ''
(assert (forall (${qk1} ${qm1} ${qm2})
  (=>
    (${update} (${delete} k1) m1 m2)
    (not (${member} k1 m2)))))
(assert (forall (${qk1} ${qk2} ${qm1} ${qm2})
  (=>
    (and (distinct k1 k2) (${update} (${delete} k1) m1 m2))
    (${match} k2 m1 m2))))
''

-- identity and seq
++ ''
(assert (forall (${qu1})
  (and
    (${seq} ${identity} u1 u1)
    (${seq} u1 ${identity} u1))))
''

in { baseAxioms }
