let lib = ./lib.dhall in

\(i : lib.MapInst) ->

let mkfun = \(name : Text) -> "${name}XZ${i.map}"

let empty = mkfun "empty"
let member = mkfun "member"
let hasVal = mkfun "hasVal"
let match = mkfun "match"
let update = mkfun "update"
let idU = mkfun "idU"

let qk1 = "(k1 ${i.key})"
let qk2 = "(k2 ${i.key})"
let qv1 = "(v1 ${i.val})"
let qv2 = "(v2 ${i.val})"
let qm1 = "(m1 ${i.map})"
let qm2 = "(m2 ${i.map})"

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

-- idU is identity update
++ ''
(assert (forall (${qm1}) (= (${update} ${idU} m1) m1)))
''

in { baseAxioms }
