let lib = ../lib.dhall

let i =
  { map = "IntMap"
  , key = "Int"
  , val = "Int"
  , upd = "IntMapUpd"
  , valUpd = "Int"
  }

let hasVal = lib.mkfun i "hasVal"
let identity = lib.mkfun i "identity"
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

-- Define modify
++ ''
(assert (forall (${qf1} ${qk1} ${qv1} ${qm1} ${qm2})
  (=>
    (and
      (${update} (${modify} k1 f1) m1 m2)
      (${hasVal} k1 v1 m1))
    (${hasVal} k1 (+ v1 f1) m2))))

(assert (forall (${qf1} ${qk1} ${qm1} ${qm2})
  (=>
    (${update} (${modify} k1 f1) m1 m2)
    (=
      (${member} k1 m1)
      (${member} k1 m2)))))

(assert (forall (${qf1} ${qk1} ${qk2} ${qm1} ${qm2})
  (=>
    (and (distinct k1 k2) (${update} (${modify} k1 f1) m1 m2))
    (${match} k2 m1 m2))))
''

++ ''
(assert (forall (${qk1})
  (= (${modify} k1 0) ${identity})))
''
