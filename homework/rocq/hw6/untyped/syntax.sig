bool : Type
list : Functor

Val(var) : Type
Tm       : Type
Frame    : Type

-- core
ret     : Val -> Tm
let_    : Tm -> (bind Val in Tm) -> Tm

-- unit
unit    : Val

-- functions (may be recursive)
abs     : (bind Val, Val in Tm) -> Val
app     : Val -> Val -> Tm

-- nats
zero    : Val
succ    : Val -> Val
ifz     : Val -> Tm -> (bind Val in Tm) -> Tm

-- products 
prod    : Val -> Val -> Val
prj     : bool -> Val -> Tm

-- sums
inj     : bool -> Val -> Val
case    : Val -> (bind Val in Tm) -> (bind Val in Tm) -> Tm

-- Frames
f_let   : (bind Val in Tm) -> Frame

