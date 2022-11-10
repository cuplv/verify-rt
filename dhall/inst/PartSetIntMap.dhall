let lib = ../lib.dhall

let i =
  { map = "IntMap"
  , key = "Int"
  , val = "Int"
  , upd = "IntMapUpd"
  , valUpd = "Int"
  }

let empty = lib.mkfun i "empty"
let singleton = lib.mkfun i "singleton"
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
let keyLeq = lib.mkfun i "keyLeq"

let qk1 = "(k1 ${i.key})"
let qk2 = "(k2 ${i.key})"
let qv1 = "(v1 ${i.val})"
let qv2 = "(v2 ${i.val})"
let qv3 = "(v3 ${i.val})"
let qm1 = "(m1 ${i.map})"
let qm2 = "(m2 ${i.map})"
let qm3 = "(m3 ${i.map})"
let qf1 = "(f1 ${i.valUpd})"

let Set2 = "(Array (SBVTuple2 Int Int) Bool)"

in

-- partMapMatch
''
(assert (forall ((n Int) (k Int) (v Int) (s ${Set2}) ${qm1})
  (=>
    (partMapMatch n s m1)
    (=
      (partHasSize k s v)
      (${hasVal} k (- n v) m1)))))
''

-- ++
-- ''
-- (assert (forall ((n Int) (v Int) (s ${Set2}) ${qm1})
--   (=>
--     (forall ((k Int))
--       (=
--         (partHasSize k s v)
--         (${hasVal} k (- n v) m1)))
--     (partMapMatch n s m1))))
-- ''

++
-- partMapMatch insert
''
(assert (forall ((n Int) (k Int) (v Int) (s1 ${Set2}) ${qm1} ${qm2})
  (=>
    (and
      (partMapMatch n s1 m1)
      (${update} (${modify} k (- 1)) m1 m2)
      (not (select s1 (mkSBVTuple2 k v))))
    (partMapMatch n (store s1 (mkSBVTuple2 k v) true) m2))))
''

++
-- partMapMatch insert, mapModify edition
''
(assert (forall ((n Int) (k Int) (v Int) (s1 ${Set2}) ${qm1} ${qm2} ${qm3})
  (=>
    (and
      (partMapMatch n s1 m1)
      (${singleton} k (- 1) m3)
      (${update} (${mapModify} m3) m1 m2)
      (not (select s1 (mkSBVTuple2 k v))))
    (partMapMatch n (store s1 (mkSBVTuple2 k v) true) m2))))
''

++
-- partMapMatch delete
''
(assert (forall ((n Int) (k Int) (v Int) (s1 ${Set2}) ${qm1} ${qm2})
  (=>
    (and
      (partMapMatch n s1 m1)
      (${update} (${modify} k 1) m1 m2)
      (select s1 (mkSBVTuple2 k v)))
    (partMapMatch n (store s1 (mkSBVTuple2 k v) false) m2))))
''
