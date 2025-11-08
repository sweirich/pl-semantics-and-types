bool : Type
nat  : Type
list : Functor

Val(var) : Type
Tm       : Type
Frame    : Type

-- Values
unit   : Val
zero   : Val
succ   : Val -> Val
prod   : Val -> Val -> Val
inj    : bool -> Val -> Val
abs    : (bind Val in Tm) -> Val

-- exception value
exn    : nat -> Val

-- Terms / Computations
ret     : Val -> Tm
let_    : Tm -> (bind Val in Tm) -> Tm
ifz     : Val -> Tm -> (bind Val in Tm) -> Tm
prj     : bool -> Val -> Tm
case    : Val -> (bind Val in Tm) -> (bind Val in Tm) -> Tm
app     : Val -> Val -> Tm

-- exceptions
raise   : Val -> Tm
try     : Tm -> nat -> Tm -> Tm


-- frames
f_try    : nat -> Tm -> Frame
f_let    : (bind Val in Tm) -> Frame
