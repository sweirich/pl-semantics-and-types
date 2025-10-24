Eff : Type

-- Types: Includes latent effect on function types
-- and recursion marks on product types
Ty     : Type
Void   : Ty
Nat    : Ty
Prod   : Eff -> Ty -> Ty -> Ty
Sum    : Ty -> Ty -> Ty
Arr    : Ty -> Eff -> Ty -> Ty
Mu     : (bind Ty in Ty) -> Ty
