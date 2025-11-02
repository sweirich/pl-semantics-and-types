-- Types
Ty     : Type
Unit   : Ty
Void   : Ty
Nat    : Ty
Prod   : Ty -> Ty -> Ty
Sum    : Ty -> Ty -> Ty
Arr    : Ty -> Ty -> Ty
Mu     : (bind Ty in Ty) -> Ty
Cont   : Ty -> Ty
Eff    : Ty -> Ty
DeCont : Ty -> Ty -> Ty

-- HOMEWORK
List   : Ty -> Ty
