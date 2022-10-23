let MapInst = { map : Text, key : Text, val : Text, upd : Text, valUpd : Text }

let mkfun = \(i : MapInst) -> \(name : Text) -> "${name}XZ${i.map}"

in { MapInst, mkfun }
