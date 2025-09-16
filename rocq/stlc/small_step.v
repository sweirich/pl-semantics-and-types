Require Export stlc.syntax.
Require Export stlc.red.

Import RedNotations.

(** Proof that the small step relation is deterministic. *)


(* We know that if a term is a value then it cannot take a step. 
   This tactic automates that reasoning. *)
Ltac invert_value_step := 
  match goal with 
  | [H : Small.step (abs ?e1) ?e2 |- _ ] => inversion H
  | [H : Small.step (lit ?k) ?e2 |- _ ] => inversion H 
  | [H : Small.step (var ?x) ?e2 |- _ ] => inversion H
  | [H1 : is_value ?v = true, H2 : Small.step ?v ?e2 |- _] => 
      inversion H2; subst; cbn in H1 ; done
  end.

Lemma small_step_determinism : 
  forall e1 e2 , e1 ⤳ e2 -> forall e2', e1 ⤳ e2' -> e2 = e2'.
Proof.
  intros e1 e2 h1.
  induction h1; intros e3 h2; inversion h2; subst.
  all: eauto.
  all: try invert_value_step.
  all: try (erewrite IHh1; eauto).
Qed.

(* ---------------------------------------------------------------------------- *)

(** Multi-step versions of each of the congruence 
   rules of the small step semantics. 
   
   For example, recall rule s_app_cong1 of the small-step relation:


           e1 ⤳ e1' 
    -------------------------- :: s_app_cong1
         e1 e2 ⤳ e1' e2

   In this module, we define lemma that creates a 
   "virtual rule" of the multi-step relation.

           e1 ⤳* e1' 
    -------------------------- :: ms_app_cong1
       e1 e2 ⤳* e1' e2

*)

(*
Small.s_app_cong1
  : forall e1 e1' e2 : Tm 0, e1 ⤳ e1' -> app e1 e2 ⤳ app e1' e2
*)

Lemma ms_app_cong1 e1 e1' e2 :  e1 ⤳* e1' ->  app e1 e2 ⤳* app e1' e2.
Proof.
  induction 1.
  eapply ms_refl.
  eapply ms_trans.
  eapply Small.s_app_cong1. eassumption.
  eapply IHmulti.
Qed.


(*
Small.s_app_cong2
  : forall v e2 e2' : Tm 0, is_value v = true -> e2 ⤳ e2' -> app v e2 ⤳ app v e2'
*)

Lemma ms_app_cong2 v e2 e2' : 
  is_value v = true ->  e2 ⤳* e2' ->  app v e2 ⤳* app v e2'.
Proof.
  intros h1 h2. 
  induction h2.
  eapply ms_refl.
  eapply ms_trans.
  eapply Small.s_app_cong2. 
  assumption. eassumption.
  eapply IHh2.
Qed.



