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
.



End Big.



(** Big step, environment-based reduction relation *)

Module BigEnv.

Inductive Val : Type :=
  | v_clo {n} : (fin n -> Val) -> Tm (S n) -> Val
  | v_lit : nat -> Val.

Definition Env n := fin n -> Val.

Inductive step {n} (ρ : Env n) : Tm n -> Val -> Prop := 

  | s_var x : 
    step ρ (var x) (ρ x)

  | s_abs e : 
    step ρ (abs e) (v_clo ρ e)

  | s_app e1 {m} (ρ' : Env m) e1' e2 v1 v2 :
    step ρ e1 (v_clo ρ' e1') ->
    step ρ e2 v1 ->
    step (v1 .: ρ') e1' v2 ->
    step ρ (app e1 e2) v2

  | s_lit k : 
    step ρ (lit k) (v_lit k)


.


End BigEnv.   

Module RedNotations.  
Infix "⤳"  := Small.step (at level 70).
Infix "⤳*" := (multi Small.step) (at level 70).
Notation "e ⟱ v" := 
  (e ⤳* v /\ is_value (v : Tm 0) = true) (at level 70).
Infix "⇓"   := Big.step   (at level 70).
Notation "< ρ | e > ⇓ v" := (BigEnv.step ρ e v) (at level 70).
End RedNotations.
