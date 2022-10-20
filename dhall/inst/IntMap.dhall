let i =
  { map = "IntMap"
  , key = "Int"
  , val = "Int"
  , upd = "IntMapUpd"
  , valUpd = "Int"
  }

in

(../MapAxioms.dhall i).baseAxioms
