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
(assert (forall ((i1 Int) (i2 Int) (s1 ${Set1}) (s2 ${Set2}))
  (=>
    (and
      (partSubset s1 s2)
      (select s1 i1))
    (partSubset s1 (store s2 (mkSBVTuple2 i1 i2) true)))))
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
      (not (select s1 (mkSBVTuple2 v k))))
    (partHasSize k (store s1 (mkSBVTuple2 v k) true) (+ n 1)))))
''

++
-- hasPartSize delete
''
(assert (forall ((n Int) (k Int) (v Int) (s1 ${Set2}))
  (=>
    (and
      (partHasSize k s1 n)
      (select s1 (mkSBVTuple2 v k)))
    (partHasSize k (store s1 (mkSBVTuple2 v k) false) (- n 1)))))
''

++
-- hasPartUB insert
''
(assert (forall ((n Int) (k Int) (v Int) (s1 ${Set2}))
  (=>
    (and
      (partHasUB k s1 n)
      (not (select s1 (mkSBVTuple2 v k))))
    (partHasUB k (store s1 (mkSBVTuple2 v k) true) (+ n 1)))))
''

-- ++
-- -- allHasUB insert
-- ''
-- (assert (forall ((n Int) (k Int) (s1 ${Set2}))
--   (=>
--     (allHasUB s1 n)
--     (partHasUB k s1 n))))
-- (assert (forall ((n Int) (s1 ${Set2}))
--   (=>
--     (forall ((k Int)) (partHasUB k s1 n))
--     (allHasUB s1 n))))
-- ''

++
-- hasPartUB delete
''
(assert (forall ((n Int) (k Int) (v Int) (s1 ${Set2}))
  (=>
    (and
      (partHasUB k s1 n)
      (select s1 (mkSBVTuple2 v k)))
    (partHasUB k (store s1 (mkSBVTuple2 v k) false) (- n 1)))))
''

++
-- hasPartDiff insert
''
(assert (forall ((n Int) (k Int) (v Int) (s1 ${Set2}))
  (=>
    (not (select s1 (mkSBVTuple2 v k)))
    (partHasDiff k s1 (store s1 (mkSBVTuple2 v k) true) 1))))
''

++
-- hasPartDiff delete
''
(assert (forall ((n Int) (k Int) (v Int) (s1 ${Set2}))
  (=>
    (select s1 (mkSBVTuple2 v k))
    (partHasDiff k s1 (store s1 (mkSBVTuple2 v k) false) (- 1)))))
''

++
''
(assert (forall ((k Int) (s1 ${Set2}))
  (partHasDiff k s1 s1 0)))
''