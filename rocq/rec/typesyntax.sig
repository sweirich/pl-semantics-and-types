-- Types
Ty     : Type
Void   : Ty
Nat    : Ty
Prod   : Ty -> Ty -> Ty
Sum    : Ty -> Ty -> Ty
Arr    : Ty -> Ty -> Ty
Mu     : (bind Ty in Ty) -> Ty
