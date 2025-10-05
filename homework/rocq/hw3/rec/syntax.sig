bool : Type

Val(var) : Type
Tm       : Type

-- Values
zero   : Val
succ   : Val -> Val
prod   : Val -> Val -> Val
inj    : bool -> Val -> Val
abs    : (bind Val in Tm) -> Val
rec    : (bind Val in Val) -> Val
fold   : Val -> Val

-- Terms / Computations
ret     : Val -> Tm
let_    : Tm -> (bind Val in Tm) -> Tm
ifz     : Val -> Tm -> (bind Val in Tm) -> Tm
prj     : bool -> Val -> Tm
split   : Val -> (bind Val,Val in Tm) -> Tm
case    : Val -> (bind Val in Tm) -> (bind Val in Tm) -> Tm
app     : Val -> Val -> Tm
unfold  : Val -> Tm

