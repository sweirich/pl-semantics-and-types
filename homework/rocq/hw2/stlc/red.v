From Stdlib Require Export ssreflect.
From Stdlib Require Export Program.Equality.
Require Export common.fintype.
Require Export common.relations.
Require Export stlc.syntax.

(* This file defines multiple reduction relations for 
   STLC + nat. 
*)
  
Import ScopedNotations.

Definition is_value {n} (e : Tm n) : bool := 
  match e with 
  | var _ => true  (* is this ok? why or why not? *)
  | abs _ => true
  | lit k => true
  | _ => false
  end.

(** Small step, substitution-based reduction relation *)

Module Small. 

Inductive step : Tm 0 -> Tm 0 -> Prop := 

 | s_beta e v : 
    is_value v = true ->
    step (app (abs e) v) (e [v..])

 | s_app_cong1 e1 e1' e2 : 
    step e1 e1' ->
    step (app e1 e2) (app e1' e2)

 | s_app_cong2 v e2 e2' : 
    is_value v = true ->
    step e2 e2' ->
    step (app v e2) (app v e2')
 | s_succ_lit k : 
    step (succ (lit k)) (lit (S k))
  
 | s_succ_cong e e' :
   step e e' -> 
   step (succ e) (succ e')

 | s_nrec_zero e0 e1 : 
    step (nrec (lit 0) e0 e1) e0

 | s_nrec_succ k e0 e1 : 
    step (nrec (lit (S k)) e0 e1) (app (e1 [(lit k) ..]) (nrec (lit k) e0 e1))

 | s_nrec_cong e e' e0 e1 :
    step e e' ->
    step (nrec e e0 e1) (nrec e' e0 e1)

 | s_letv v e :
    is_value v = true ->
    step (let_ v e) (e [v ..])

 | s_let_cong e1 e1' e2 :
    step e1 e1' ->
    step (let_ e1 e2) (let_ e1' e2)
.

End Small.

(** Big step, substitution-based reduction relation *)

Module Big.

Inductive step : Tm 0 -> Tm 0 -> Prop := 
  | s_val v : 
    is_value v = true -> 
    step v v

  | s_app  e1 e1' e2 v1 v2 :
    step e1 (abs e1') ->
    step e2 v1 ->
    step (e1' [v1 .. ]) v2 ->
    step (app e1 e2) v2
  | s_succ e k :
    step e (lit k) ->
    step (succ e) (lit (S k))

  | s_nrec_zero e e0 e1 v : 
    step e (lit 0) -> 
    step e0 v ->
    step (nrec e e0 e1) v

  | s_nrec_succ e e0 e1 k v e' v1 : 
    step e (lit (S k)) -> 
    step e1[(lit k)..] (abs e') ->
    step (nrec (lit k) e0 e1) v1 ->
    step e'[v1..] v ->
    step (nrec e e0 e1) v

  | s_let e1 e2 v1 v2 :  
    step e1 v1 -> 
    step (e2 [v1 ..]) v2 ->
    step (let_ e1 e2) v2
.


End Big.



Module RedNotations.  
Infix "⤳"  := Small.step (at level 70).
Infix "⤳*" := (multi Small.step) (at level 70).
Notation "e ⟱ v" := 
  (e ⤳* v /\ is_value (v : Tm 0) = true) (at level 70).
Infix "⇓"   := Big.step   (at level 70).
End RedNotations.


