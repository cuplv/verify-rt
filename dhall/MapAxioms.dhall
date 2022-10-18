let lib = ./lib.dhall in

\(i : lib.MapInst) ->

let mkfun = \(name : Text) -> "${name}XZ${i.map}"

let empty = mkfun "empty"
let member = mkfun "member"
let hasVal = mkfun "hasVal"
let match = mkfun "match"
let update = mkfun "update"
let identity = mkfun "identity"
let insert = mkfun "insert"
let delete = mkfun "delete"
let seq = mkfun "seq"

let qk1 = "(k1 ${i.key})"
let qk2 = "(k2 ${i.key})"
let qv1 = "(v1 ${i.val})"
let qv2 = "(v2 ${i.val})"
let qm1 = "(m1 ${i.map})"
let qm2 = "(m2 ${i.map})"
let qu1 = "(u1 ${i.upd})"
let qu2 = "(u2 ${i.upd})"

let baseAxioms =

-- Define empty map, as no members
''
(assert (forall (${qk1}) (not (${member} k1 ${empty}))))
''

-- Define match 
++ ''
(assert (forall (${qk1} ${qm1} ${qm2})
  (= (${match} k1 m1 m2)
    (and
      (forall (${qv1}) (= (${hasVal} k1 v1 m1) (${hasVal} k1 v1 m2)))
      (= (${member} k1 m1) (${member} k1 m2))))))
''

-- Equivalence from matching on all keys
++ ''
(assert (forall (${qm1} ${qm2})
  (= (= m1 m2)
     (forall (${qk1}) (${match} k1 m1 m2)))))
''

-- hasVal implies member
++ ''
(assert (forall (${qk1} ${qv1} ${qm1})
  (=> (${hasVal} k1 v1 m1) (${member} k1 m1))))
''

-- member implies exists hasVal
-- ??? Do we need this? Leaving it out for now.

-- Define identity update
++ ''
(assert (forall (${qm1}) (= (${update} ${identity} m1) m1)))
''

-- Define insert update
++ (
let m2 = "(${update} (${insert} k1 v1) m1)"
in ''
(assert (forall (${qk1} ${qv1} ${qm1})
  (and
    (${hasVal} k1 v1 ${m2})
    (forall (${qk2}) (=> (distinct k1 k2) (${match} k2 m1 ${m2}))))))
''
)

-- Defint delete update
++ (
let m2 = "(${update} (${delete} k1) m1)"
in ''
(assert (forall (${qk1} ${qm1})
  (not (${member} k1 ${m2}))))
''
)

-- Define seq update
++ (
let m2 = "(${update} u1 m1)"
let m3a = "(${update} u2 ${m2})"
let m3b = "(${update} (${seq} u1 u2) m1)"
in ''
(assert (forall (${qu1} ${qu2} ${qm1}) (= ${m3a} ${m3b})))
''
)

in { baseAxioms }
