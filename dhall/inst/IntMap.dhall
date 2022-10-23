let lib = ../lib.dhall

let i =
  { map = "IntMap"
  , key = "Int"
  , val = "Int"
  , upd = "IntMapUpd"
  , valUpd = "Int"
  }

let hasVal = lib.mkfun i "hasVal"
let match = lib.mkfun i "match"
let member = lib.mkfun i "member"
let modify = lib.mkfun i "modify"
let offset = lib.mkfun i "offset"
let update = lib.mkfun i "update"
let valUpdate = lib.mkfun i "valUpdate"

let qk1 = "(k1 ${i.key})"
let qk2 = "(k2 ${i.key})"
let qv1 = "(v1 ${i.val})"
let qv2 = "(v2 ${i.val})"
let qm1 = "(m1 ${i.map})"
let qm2 = "(m2 ${i.map})"
let qf1 = "(f1 ${i.valUpd})"

in

(../MapAxioms.dhall i).baseAxioms

-- -- Define valUpdate for IntMap
-- ++ ''
-- (assert (forall (${qf1} ${qv1})
--   (= (${valUpdate} f1 v1) (+ f1 v1))))
-- ''

-- -- Define valUpdate again?
-- ++ (
-- let u = "(${modify} k1 f1)"
-- let m2 = "(${update} ${u} m1)"
-- in ''
-- (assert (forall (${qf1} ${qk1} ${qv1} ${qm1})
--   (and
--     (=>
--       (${hasVal} k1 v1 m1)
--       (${hasVal} k1 (+ f1 v1) ${m2}))
--     (=>
--       (not (${member} k1 m1))
--       (not (${member} k1 ${m2})))
--     (forall (${qk2})
--       (=>
--         (distinct k1 k2)
--         (${match} k2 m1 ${m2}))))))
-- ''
-- )

-- Define offset
++ ''
(assert (forall (${qf1} ${qk1} ${qm1} ${qm2})
  (=
    (${offset} f1 k1 m1 m2)
    (and
      (${member} k1 m1)
      (${member} k1 m2)
      (forall (${qv1})
        (=
          (${hasVal} k1 v1 m1)
          (${hasVal} k1 (+ f1 v1) m2)))))))
''

-- offset 0 is reflexive
++ ''
(assert (forall (${qk1} ${qm1})
  (${offset} 0 k1 m1 m1)))
''

-- Define modify via offset
++ (
let u = "(${modify} k1 f1)"
let m2 = "(${update} ${u} m1)"
in ''
(assert (forall (${qf1} ${qk1} ${qm1})
  (and
    (or
      (${offset} f1 k1 m1 ${m2})
      (and (not (${member} k1 m1)) (not (${member} k1 ${m2}))))
    (forall (${qk2})
      (=>
        (distinct k1 k2)
        (${match} k2 m1 ${m2})))
    )))
''
)
