let lib = ../lib.dhall

let i =
  { map = "IntMap"
  , key = "Int"
  , val = "Int"
  , upd = "IntMapUpd"
  , valUpd = "Int"
  }

let empty = lib.mkfun i "empty"
let hasVal = lib.mkfun i "hasVal"
let identity = lib.mkfun i "identity"
let match = lib.mkfun i "match"
let member = lib.mkfun i "member"
let modify = lib.mkfun i "modify"
let offset = lib.mkfun i "offset"
let update = lib.mkfun i "update"
let valUpdate = lib.mkfun i "valUpdate"
let diffMap = lib.mkfun i "diffMap"
let totalSum = lib.mkfun i "totalSum"
let mapBound = lib.mkfun i "mapBound"
let mapModify = lib.mkfun i "mapModify"
let mapLowerBound = lib.mkfun i "mapLowerBound"
let mapNegate = lib.mkfun i "mapNegate"

let qk1 = "(k1 ${i.key})"
let qk2 = "(k2 ${i.key})"
let qv1 = "(v1 ${i.val})"
let qv2 = "(v2 ${i.val})"
let qv3 = "(v3 ${i.val})"
let qm1 = "(m1 ${i.map})"
let qm2 = "(m2 ${i.map})"
let qm3 = "(m3 ${i.map})"
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

-- Define mapModify
++ ''
(assert (forall (${qm1} ${qm2} ${qm3} ${qk1} ${qv1} ${qv2})
  (=>
    (and
      (${update} (${mapModify} m1) m2 m3)
      (${hasVal} k1 v1 m1)
      (${hasVal} k1 v2 m2))
    (${hasVal} k1 (+ v1 v2) m3))))

(assert (forall (${qm1} ${qm2} ${qm3} ${qk1})
  (=>
    (and
      (${update} (${mapModify} m1) m2 m3)
      (not (${member} k1 m1)))
    (${match} k1 m2 m3))))

(assert (forall (${qm1} ${qm2} ${qm3} ${qk1})
  (=>
    (${update} (${mapModify} m1) m2 m3)
    (= (${member} k1 m2) (${member} k1 m3)))))

(assert (forall (${qm1})
  (=
    (${empty} m1)
    (= (${mapModify} m1) ${identity}))))
''

-- Define diffMap
++ ''
(assert (forall (${qk1} ${qm1} ${qm2} ${qm3})
  (=>
    (${diffMap} m1 m2 m3)
    (=>
      (or (not (${member} k1 m1)) (not (${member} k1 m2)))
      (not (${member} k1 m3))))))

(assert (forall (${qk1} ${qv1} ${qv2} ${qm1} ${qm2} ${qm3})
  (=>
    (and (${diffMap} m1 m2 m3) (${hasVal} k1 v1 m1) (${hasVal} k1 v2 m2))
    (${hasVal} k1 (- v1 v2) m3))))

(assert (forall (${qm1} ${qm2} ${qm3})
  (=>
    (and (${diffMap} m1 m2 m3) (or (${empty} m1) (${empty} m2)))
    (${empty} m3))))
''

-- Define totalSum (note, this doesn't take into account missing keys)
++ ''
(assert (forall (${qk1} ${qm1} ${qm2} ${qv1} ${qf1})
  (=>
    (and (${totalSum} m1 v1) (${update} (${modify} k1 f1) m1 m2))
    (${totalSum} m2 (+ v1 f1)))))

(assert (forall (${qm1} ${qm2} ${qm3} ${qv1} ${qv2})
  (=>
    (and
      (${totalSum} m1 v1)
      (${totalSum} m2 v2)
      (${update} (${mapModify} m1) m2 m3))
    (${totalSum} m3 (+ v1 v2)))))

(assert (forall (${qm1} ${qv1} ${qv2})
  (=>
    (and (${totalSum} m1 v1) (${totalSum} m1 v2))
    (= v1 v2))))
''

-- Define mapBound (could also define using offset)
++ ''
(assert (forall (${qm1} ${qm2} ${qm3} ${qk1} ${qv1} ${qv2} ${qv3})
  (=>
    (and
      (${mapBound} m1 m2 m3)
      (${hasVal} k1 v1 m1)
      (${hasVal} k1 v2 m2)
      (${hasVal} k1 v3 m3))
    (<= (- v2 v1) v3))))
(assert (forall (${qm1} ${qm2} ${qm3} ${qk1})
  (=>
    (${mapBound} m1 m2 m3)
    (= (${member} k1 m2) (${member} k1 m3)))))
''

-- Define mapLowerBound
++ ''
(assert (forall (${qk1} ${qv1} ${qv2} ${qm1})
  (=>
    (and (${mapLowerBound} v2 m1) (${hasVal} k1 v1 m1))
    (>= v1 v2))))
''

-- Define mapNegate
++ ''
(assert (forall (${qk1} ${qv1} ${qm1} ${qm2})
  (=>
    (and (${mapNegate} m1 m2) (${hasVal} k1 v1 m1))
    (${hasVal} k1 (- 0 v1) m2))))
(assert (forall (${qk1} ${qm1} ${qm2})
  (=>
    (${mapNegate} m1 m2)
    (= (${member} k1 m1) (${member} k1 m2)))))
''
