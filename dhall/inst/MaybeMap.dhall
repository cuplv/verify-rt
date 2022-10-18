let i =
  { map = "MaybeMap"
  , key = "Int"
  , val = "Bool"
  , upd = "MaybeMapUpd"
  }

in

(../MapAxioms.dhall i).baseAxioms
