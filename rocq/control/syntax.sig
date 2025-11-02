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
rec    : (bind Val in Val) -> Val
fold   : Val -> Val

-- continuation value, a saved stack
cont   : "list"(Frame) -> Val
-- effect constructors
eff    : nat -> Val

-- Terms / Computations
ret     : Val -> Tm
let_    : Tm -> (bind Val in Tm) -> Tm
ifz     : Val -> Tm -> (bind Val in Tm) -> Tm
prj     : bool -> Val -> Tm
case    : Val -> (bind Val in Tm) -> (bind Val in Tm) -> Tm
app     : Val -> Val -> Tm
unfold  : Val -> Tm

-- exceptions
raise   : Val -> Tm
try     : Tm -> (bind Val in Tm) -> Tm

-- continuations
throw   : Val -> Val -> Tm
letcc   : (bind Val in Tm) -> Tm

-- effect handlers
perform  : Val -> Tm
handle   : Tm -> (bind Val in Tm) -> nat -> (bind Val in Tm) -> Tm
continue : Val -> Val -> Tm

-- frames
f_try    : (bind Val in Tm) -> Frame
f_let    : (bind Val in Tm) -> Frame
f_handle : (bind Val in Tm) -> nat -> (bind Val in Tm) -> Frame


-- HOMEWORK
v_nil       : Val
v_cons      : Val -> Val -> Val
throw_e     : Val -> Tm -> Tm
exit        : Val -> Tm 
discontinue : Val -> Val -> Tm
