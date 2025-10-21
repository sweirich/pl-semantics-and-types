nat : Type

Ty    : Type
Nat    : Ty
Arr    : Ty -> Ty -> Ty
Box    : Ty -> Ty

Val(var) : Type
abs     : (bind Val in Tm) -> Val
lit     : nat -> Val
box     : Val -> Val
fun_    : (bind Val , Val in Tm) -> Val

Tm      : Type 
ret     : Val -> Tm
let_    : Tm -> (bind Val in Tm) -> Tm
app     : Val -> Val -> Tm
unbox   : Tm -> (bind Val in Tm) -> Tm
