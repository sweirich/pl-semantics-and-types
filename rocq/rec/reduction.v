From Stdlib Require Export ssreflect.
From Stdlib Require Export Program.Equality.
Require Export common.core.
Require Export common.fintype.
Require Export common.fin_util.
Require Export common.relations.
Require Export common.renaming.
Require Export rec.syntax.
Import ScopedNotations.

(* We'll use more automation in these proofs. *)
Create HintDb rec.

Module Small. 

(** Small step, substitution-based reduction *)

Inductive step : Tm 0 -> Tm 0 -> Prop := 

 | s_letv v e :
    step (let_ (ret v) e) (e [v..])

 | s_let_cong e1 e1' e2 :
    step e1 e1' ->
    step (let_ e1 e2) (let_ e1' e2)

 | s_beta e v : 
    step (app (abs e) v) (e [v..])

 | s_succ k : 
    step (succ (lit k)) (ret (lit (S k)))

 | s_ifz_zero e1 e2 : 
    step (ifz (lit 0) e1 e2) e1

 | s_ifz_succ e1 e2 k : 
    step (ifz (lit (S k)) e1 e2) (e2 [ (lit k)..])

 | s_prj1 v1 v2 : 
    step (prj true (prod v1 v2)) (ret v1)

 | s_prj2 v1 v2 : 
    step (prj false (prod v1 v2)) (ret v2)

 | s_case_inj1 v e1 e2 :
    step (case (inj true v) e1 e2) (e1 [v..])

 | s_case_inj2 v e1 e2 :
    step (case (inj false v) e1 e2) (e2[v..])

 | s_app_rec (v : Val 1) (v1 : Val 0) : 
    step (app (rec v) v1) (app v[(rec v)..] v1)

 | s_prj_rec b v : 
    step (prj b (rec v)) (prj b v[(rec v)..])

 | s_split_rec v e :
    step (split (rec v) e) (split (v [(rec v)..]) e)

 | s_case_rec v e1 e2 :
    step (case (rec v) e1 e2) (case (v [(rec v)..]) e1 e2)

 | s_unfold v :
     step (unfold (fold v)) (ret v)
 
.

End Small.

#[export] Hint Constructors Small.step : rec.

Declare Scope rec_scope.

Module Notations.
Export ScopedNotations.
Notation "'prj1'" := (prj true) (at level 70) : rec_scope.
Notation "'prj2'" := (prj false) (at level 70) : rec_scope.
Notation "'inj1'" := (inj true) (at level 70) : rec_scope.
Notation "'inj2'" := (inj false) (at level 70) : rec_scope.
Notation "e ~> e'" := (Small.step e e') (at level 70) : rec_scope.
Notation "e ~>* e'" := (multi Small.step e e') (at level 70) : rec_scope.
End Notations.

Open Scope rec_scope.
Import Notations.

(** multistep congruence *)
Lemma ms_let_cong e1 e1' e2 : 
  e1 ~>* e1' -> let_ e1 e2 ~>* let_ e1' e2.
Proof.
  induction 1. eapply ms_refl.
  eapply ms_trans; eauto.
  econstructor; eauto.
Qed.

(** ret is a terminal state *)
Lemma ret_steps_to_itself v e :
  ret v ~>* e -> e = ret v.
Proof. intro h. inversion h. done. inversion H. Qed.


Lemma deterministic e e1 e2 : 
  e ~> e1 -> e ~> e2 -> e1 = e2.
Proof.
  move=> h.
  move: e2.
  induction h.
  all: intros e2' h2.
  all: inversion h2; subst.
  all: eauto.
  - inversion H2.
  - inversion h.
  - apply IHh in H2. f_equal. auto.
Qed.

