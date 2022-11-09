let Set = "(Array (SBVTuple2 Int Int) Bool)"

in

''
(assert (forall ((i1 Int) (i2 Int) (s1 ${Set}) (s2 ${Set}))
  (=>
    (partLocked i1 s1 s2)
    (=
      (select s1 (mkSBVTuple2 i1 i2))
      (select s2 (mkSBVTuple2 i1 i2))))))
''
