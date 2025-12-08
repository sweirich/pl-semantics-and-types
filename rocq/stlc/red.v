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
  | abs _ => true
  | lit k => true
  | unit  => true
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

(*
Lemma is_value_nostep : 
  forall v, is_value v = true -> forall e, not (step v e).
Proof.
  intro v. dependent induction v.
  all: cbn; intro h; try done.
  all: intros e h1.
  all: try inversion h1.
Qed.

Lemma deterministic : 
  forall e1 e2 e2', step e1 e2  -> step e1 e2' -> e2 = e2'.
Proof.
  intros e1 e2 e2' h.
  move: e2'.
  induction h.
  all: intros e2'' h2; inversion h2; subst.
  all: eauto.
  all: try solve [inversion H3].
  all: try solve [  erewrite IHh; eauto ].
  all: try solve [  eapply is_value_nostep in h; done ].
  all: try solve [match goal with 
    [ H: is_value ?v = true, H1 : step ?v ?e |- _ ] => 
      eapply is_value_nostep in H1; done
  end].
  eapply is_value_nostep in H0; done.
Qed.
*)

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




Module RedNotations.  
Infix "~>"  := Small.step (at level 70).
Infix "~>*" := (multi Small.step) (at level 70).
Notation "e ⟱ v" := 
  (e ~>* v /\ is_value (v : Tm 0) = true) (at level 70).
Infix "⇓"   := Big.step   (at level 70).
End RedNotations.


