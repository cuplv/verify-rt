let Set1 = "(Array Int Bool)"
let Set2 = "(Array (SBVTuple2 Int Int) Bool)"

in

''
(assert (forall ((i1 Int) (i2 Int) (s1 ${Set2}) (s2 ${Set2}))
  (=>
    (partLocked i1 s1 s2)
    (=
      (select s1 (mkSBVTuple2 i1 i2))
      (select s2 (mkSBVTuple2 i1 i2))))))
''

++
''
(assert (forall ((i1 Int) (i2 Int) (i3 Int) (s1 ${Set1}) (s2 ${Set2}))
  (=>
    (partSubset s1 s2)
    (=>
      (select s2 (mkSBVTuple2 i1 i2))
      (select s1 i1)))))
''

++
''
(assert (forall ((s1 ${Set1}) (s2 ${Set2}))
  (=>
    (forall ((i1 Int) (i2 Int))
      (=>
        (select s2 (mkSBVTuple2 i1 i2))
        (select s1 i1)))
    (partSubset s1 s2))))
''

++
-- hasPartSize insert
''
(assert (forall ((n Int) (k Int) (v Int) (s1 ${Set2}))
  (=>
    (and
      (partHasSize k s1 n)
      (not (select s1 (mkSBVTuple2 k v))))
    (partHasSize k (store s1 (mkSBVTuple2 k v) true) (+ n 1)))))
''

++
-- hasPartSize delete
''
(assert (forall ((n Int) (k Int) (v Int) (s1 ${Set2}))
  (=>
    (and
      (partHasSize k s1 n)
      (select s1 (mkSBVTuple2 k v)))
    (partHasSize k (store s1 (mkSBVTuple2 k v) false) (- n 1)))))
''
