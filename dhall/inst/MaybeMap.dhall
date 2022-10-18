let i =
  { map = "MaybeMap"
  , key = "Int"
  , val = "(SBVMaybe MaybeMapVal)"
  -- "just_SBVMaybe"
  , upd = "MaybeMapUpd"
  , valUpd = "MaybeMapValUpd"
  }

in

(../MapAxioms.dhall i).baseAxioms
