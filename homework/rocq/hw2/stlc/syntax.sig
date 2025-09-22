-- Specification of the syntax of STLC for the autosubst-ocaml tool
-- https://github.com/uds-psl/autosubst-ocaml

-- include natural numbers 
nat : Type

-- types
Ty  : Type
Nat : Ty
Arr : Ty -> Ty -> Ty

-- declare name of var constructor
Tm(var) : Type 
-- abstractions create a new scope
abs     : (bind Tm in Tm) -> Tm
-- application
app     : Tm -> Tm -> Tm
-- literal numbers
lit     : nat -> Tm   
-- successor operation
succ    : Tm -> Tm
-- primitive recursion for natural numbers
nrec    : Tm -> Tm -> (bind Tm in Tm) -> Tm
-- local let binding (NB: "let" is a Rocq keyword)
let_    : Tm -> (bind Tm in Tm) -> Tm
