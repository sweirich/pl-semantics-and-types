Require Export untyped.prim.
Require Export Classes.RelationClasses.

Import SyntaxNotations.
Import Lists.List.ListNotations.
Open Scope list_scope.
Open Scope rec_scope.

(** * Semantics based on an abstract machine with an explicit stack *)

(** A frame corresponds to the [let_cong] rule of the small step semantics.
   It remembers that after evaluating [e1] we need to continue with evaluting
   the body of a let expression. This body has a single bound variable. *)

Definition frame   := Frame 0.
Definition stack   := list frame.
Definition machine := (stack * Tm 0)%type.

(** An abstract machine is done evaluating when the stack is empty and 
    the expression is a value. *)
Inductive final : machine -> Prop := 
  | final_machine v :
    final ( [] , ret v ).

Module Small.

Local Reserved Notation "m ↦ m'" (at level 70).

Inductive step : machine -> machine -> Prop := 
  | s_prim s e e' : 
    e ~>> e' ->
    (s, e) ↦ (s, e')

  | s_pop s e2 v : 
    (f_let e2 :: s, ret v) ↦ (s, e2[v..])

  | s_push  s e1 e2 : 
    (s, let_ e1 e2 ) ↦ (f_let e2 :: s, e1)
where "m ↦ m'" := (step m m') : rec_scope.
  
Definition irreducible (m : machine) : Prop := 
  forall m', not (m ↦ m').

(** Machine steps are deterministic *)
Lemma deterministic :
  forall m m1 m2, (m ↦ m1) -> (m ↦ m2) -> m1 = m2.
Proof.
  intros m m1 m2 h1 h2. 
  inversion h1; subst; inversion h2; subst; auto.
  all: try match goal with [ H : ret _ ~>> _ |- _ ] => inversion H end.
  all: try match goal with [ H : let_ _ _ ~>> _ |- _ ] => inversion H end.
  eapply primitive_deterministic in H; eauto. subst. auto.
Qed.


(** The program halts in exactly n steps *)
Definition halts_n (m : machine) n : Prop := 
  exists v, step_n step n m (nil, ret v).

(** The program halts in an unspecified number of steps *)
Definition halts (m : machine) : Prop := 
  exists v, multi step m (nil, ret v).

(** An approximation relation based on halting behavior *)
Definition approx (m1 m2 : machine) : Prop := 
  halts m1 -> halts m2.

(** A step-indexed approximation: the first machine must halt
    within the specified number of steps. *)
Definition approx_n m1 m2 n : Prop := 
  halts_n m1 n -> halts m2.
  
End Small.

Module Notations.
Infix "↦"  := Small.step (at level 70) : rec_scope.
Infix "↦*" := (multi Small.step) (at level 70) : rec_scope.
Infix "⊑"  := Small.approx (at level 70) : rec_scope.
Notation "m ⊑n m' @"  := (Small.approx_n m m') (at level 70) : rec_scope.
End Notations.

Import Notations.

Lemma halts_reverse_prim s e e' : 
  Small.halts (s, e') ->
  e ~>> e' ->
  Small.halts (s, e).
Proof.
  intros h ss.
  destruct h as [m sn].
  exists m. econstructor; eauto. econstructor; eauto.
Qed.

Lemma halts_reverse m m' : 
  Small.halts m ->
  m' ↦ m ->
  Small.halts m'.
Proof.
  intros h ss.
  destruct h as [k sn].
  exists k. econstructor; eauto. 
Qed.

Lemma terminal_halts {v} : 
  Small.halts (nil, ret v).
Proof.
  exists v. eapply ms_refl; eauto.
Qed.

Lemma halts_forward {m m'}:
  Small.halts m -> m ↦ m' -> 
  Small.halts m'.
Proof.
  intros h ss.
  inversion h; subst. inversion H; subst. inversion ss. inversion H3.
  apply Small.deterministic with (m1 := e2) in ss; eauto. subst.
  eexists. eauto.
Qed.

Lemma halts_n_forward {m m' k}:
  Small.halts_n m k -> m ↦ m' -> 
  exists j, S j = k /\ Small.halts_n m'  j.
Proof.
  intros h ss.
  inversion h; subst. inversion H; subst. inversion ss. inversion H3.
  apply Small.deterministic with (m1 := e2) in ss; eauto. subst.
  eexists. split; eauto. econstructor; eauto. 
Qed.

Lemma halts_n_reverse {m m' k}:
  Small.halts_n m'  k ->  m ↦ m' ->
  Small.halts_n m (S k).
Proof.
  intros [v h] ss.
  exists v. econstructor; eauto.
Qed.

(** * Properties of the approximation relation *)

Instance approx_refl : Reflexive Small.approx.
Proof. unfold Small.approx. done. Qed.

Instance approx_trans : Transitive Small.approx.
Proof. unfold Small.approx. unfold Transitive. intros. eauto. Qed.

Lemma approx_n_refl { m k } : m ⊑n m @ k.
Proof.
  unfold Small.approx_n. intro h. unfold Small.halts.
  unfold Small.halts_n in h.
  destruct h as [v SS].
  eapply step_n_multi in SS.
  eexists; eauto.
Qed.

Lemma approx_n_trans { m1 m2 m3 } : 
  (forall k, m1 ⊑n m2 @ k) -> (forall k, m2 ⊑n m3 @ k)  -> (forall k,  m1 ⊑n m3 @ k).
Proof.
  unfold Small.approx_n.
  unfold Small.halts_n.
  unfold Small.halts.
  intros h1 h2 k HH. 
  move: (h1 k HH) => [v1 SS].
  move: (multi_step_n Small.step _ _ SS) => [k2 SS2].
  eapply (h2 k2). eexists; eauto.
Qed.

Lemma approx_forward { m1 m2 } : m1 ↦ m2 -> m1 ⊑ m2.
unfold Small.approx. intros. eapply halts_forward; eauto. Qed.

Lemma approx_forward_prim { s e1 e2 } : e1 ~>> e2 -> (s,e1) ⊑ (s, e2).
unfold Small.approx. intros. eapply halts_forward; eauto.
eapply Small.s_prim; eauto. Qed.

Lemma approx_reverse { m1 m2 } : m1 ↦ m2 -> m2 ⊑ m1.
unfold Small.approx. intros. eapply halts_reverse; eauto. Qed.

Lemma approx_reverse_prim { s e1 e2 } : e1 ~>> e2 -> (s,e2) ⊑ (s,e1).
unfold Small.approx. intros. eapply halts_reverse; eauto. eapply Small.s_prim; eauto. Qed.


Lemma approx_n_forward { m1 m2 k } : m1 ↦ m2 -> m1 ⊑n m2 @ k.
unfold Small.approx_n. intros. 
eapply halts_n_forward in H0; eauto. destruct H0 as [j [EQ [v h0]]].
exists v. eapply step_n_multi; eauto. Qed.

Lemma approx_n_forward_prim { s e1 e2 k } : e1 ~>> e2 -> (s,e1) ⊑n (s, e2) @ k.
intros. eapply approx_n_forward. eapply Small.s_prim; eauto. Qed.

Lemma approx_n_reverse { m1 m2 k} : m1 ↦ m2 -> m2 ⊑n m1 @ k.
unfold Small.approx_n. intros. 
eapply halts_n_reverse in H0; eauto. destruct H0 as [v h0]. 
exists v. eapply step_n_multi; eauto. Qed.

Lemma approx_n_reverse_prim { s e1 e2 k } : e1 ~>> e2 -> (s,e2) ⊑n (s,e1) @k.
intros. eapply approx_n_reverse; eauto. eapply Small.s_prim; eauto.
Qed.

