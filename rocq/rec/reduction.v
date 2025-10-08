(** * Imports *)

From Stdlib Require Export ssreflect.
From Stdlib Require Export Program.Equality.
Require Export common.core.
Require Export common.fintype.

Require Export common.fin_util.
Require Export common.relations.
Require Export common.renaming.

(** The syntax file defines notations for printing. However, this syntax can 
    sometimes be confusing so we disable it here. *)
Require Export rec.syntax.
Disable Notation "↑__Val" (all).
Disable Notation "↑__Tm" (all).
Disable Notation "'__Val'" (all).
Disable Notation "var" (all).

(** Define a notation scope specific to this language. *)
Declare Scope rec_scope.

Module SyntaxNotations.
Export ScopedNotations.
Notation "'prj1'" := (prj true) (at level 70) : rec_scope.
Notation "'prj2'" := (prj false) (at level 70) : rec_scope.
Notation "'inj1'" := (inj true) (at level 70) : rec_scope.
Notation "'inj2'" := (inj false) (at level 70) : rec_scope.
Notation "⇑" := (up_Val_Val) : rec_scope.
End SyntaxNotations.

Export SyntaxNotations.

(** * Syntax properties *)

(** Decide whether a value is a natural number value *)
Fixpoint is_nat (v : Val 0) : bool := 
  match v with 
  | zero => true
  | succ v1 => is_nat v1 
  | _ => false
  end.

(** * Notes about using Autosubst *)

Section AutosubstNotes.

(* Autosubst defines substitution and renaming operations over 
   syntax descriptions. 
 *)

Context 
  (m n : nat) 
  (ξ : fin m -> fin n)  
  (* renaming: changes variable names *)
  (σ : fin m -> Val n). 
  (* substitution: replaces variables with values *)

(* These functions are defined in syntax.v *)
Check (ren_Val ξ).
Check (ren_Tm ξ).
Check (subst_Val σ).
Check (subst_Tm σ).

Context (v : Val m) (e : Tm m).

(* Autosubst includes a *type class* and notation. That 
   means that we can use the same name to refer to both 
   subst_Val and subst_Tm. *)
Check (subst1 σ v).
Check (subst1 σ e).
(* And this notation expands to 'subst1'. *)
Check (v[σ]).
Check (e[σ]).

(* However, autosubst also uses the v[σ] notation for 
   *printing* uses of subst_Val. Any v[σ] you type will 
   be subst1, but if you see a v[σ] in the context, it 
   could be subst_Val or subst_Tm.
*)
Check (subst_Val σ v). (* Roq prints v[σ] : Val n *)

(* Most of the time, this difference is not a problem. The 
   reason is that subst1 unfolds to subst_Val/subst_Tm.
*)
Example example : (subst1 σ v = subst_Val σ v).
(* To see which we really have, ask for the details. *)
Set Printing All.
cbn. (* does nothing. *)
simpl. (* does nothing. *)
auto_unfold. (* replaces subst1 with subst_Val
                asimpl would also work. *)
eapply eq_refl.
Unset Printing All.
Qed.

(* Some tactics work up to unfolding definitions, 
   so this difference doesn't cause trouble. *)
Example example2 : (subst1 σ v = subst_Val σ v).
reflexivity.
Qed.

(* But sometimes it matters. For example, the 
   idSubst_Tm lemma removes an identity substitution
   applied to a term.
   If you try to apply it by hand, it produces an 
   uniformative error message.
   'asimpl' knows to unfold first, but if you want this 
   level of control, you need to do that too.
*)
Example example3 : forall tau,
  (forall v, tau v = var v) -> 
  (app v v)[tau] = app v v.
Proof.
  intros tau R.
  try (rewrite idSubst_Tm). (* does nothing *)
  auto_unfold.
  rewrite idSubst_Tm. auto. (* works now *)
  done.
Qed.

Context (v0 : Val (S m)).

Example push_in : 
  (v0[up_Val_Val σ] = zero) ->
  (abs (ret v0))[σ] = abs (ret zero).
Proof. intro h.
       (* push the substitution in. but this 
          also unfolds subst1, Subst_Val *)
       cbn.
       try (rewrite h).  
       (* does nothing *)
       destruct (v0[up_Val_Val σ]) eqn:EQ; try done. 
       (* doesn't change the goal *)
       unfold subst1,Subst_Val in EQ. 
       rewrite EQ.
       done.
Qed.

End AutosubstNotes.

(** * Small step semantics *)

(** We want to use automation in these proofs. This line creates a
    database of constructors and lemmas that we can instruct Rocq 
    to automatically apply. *)
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

 | s_ifz_zero e1 e2 : 
    step (ifz zero e1 e2) e1

 | s_ifz_succ e1 e2 k : 
    step (ifz (succ k) e1 e2) (e2 [ k..])

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

(** Add all of the constructors to the hint database, so that 
    the command 'eauto with rec' can automatically apply them 
    to construct derivations *)
#[export] Hint Constructors Small.step : rec.

Module Notations.
Export SyntaxNotations.
Notation "e ~> e'" := (Small.step e e') (at level 70) : rec_scope.
Notation "e ~>* e'" := (multi Small.step e e') (at level 70) : rec_scope.
End Notations.

Open Scope rec_scope.
Import Notations.

(** * Properties of small-step reduction *)

(** multistep congruence for let *)
Lemma ms_let_cong e1 e1' e2 : 
  e1 ~>* e1' -> let_ e1 e2 ~>* let_ e1' e2.
Proof.
  induction 1. eapply ms_refl.
  eapply ms_trans; eauto.
  econstructor; eauto.
Qed.

(** The small step relation is deterministic *)
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

(** ret is a terminal state *)
Lemma ret_steps_to_itself v e :
  ret v ~>* e -> e = ret v.
Proof. intro h. inversion h. done. inversion H. Qed.

(** An irreducible term is one that cannot step. It is either a value or a stuck term. *)
Definition irreducible (e:Tm 0) := forall e', not (Small.step e e').

(** We can decide whether a term steps or is irreducible *)
Lemma canstep (e : Tm 0) : 
  (exists e', Small.step e e') \/ (irreducible e).
dependent induction e.
all: try solve [right; intros ? h; inversion h].
all: try (destruct v; try destruct n; try destruct b;
     try solve [right; intros ? h; inversion h];
     try solve [left; eauto with rec]). 
- edestruct IHe1 as [[e1' S1] | I1]; auto.
  left; eauto with rec. destruct e1.
  left; eauto with rec.
  all: right; intros ? h; inversion h; subst; eapply I1; eauto.
Qed.

(** This tactic identifies a contraction: we assume "irreducible e" but we can easily show that e reduces *)
Ltac is_reducible := 
  match goal with 
  | [ h : ?e ~> _  |- irreducible ?e -> _ ] => 
      let IR := fresh in
      intro IR; assert False; [eapply IR; eauto with rec|]; done
  | [ H : ?e ~> _ , H2 : irreducible ?e |- _ ] => 
      assert False; [eapply H2; eauto with rec|]; done
  | [ H2 : irreducible ?e |- forall e', ?e ~> e' -> _ ] => 
      let e := fresh in
      let SS := fresh in 
      intros e SS; is_reducible
  | [ h : exists e' , ?e ~> _  |- irreducible ?e -> _ ] => 
      destruct h; is_reducible
  | [ |- irreducible ?e -> _ ] => 
      let IR := fresh in
      intro IR; assert False; [eapply IR; eauto with rec|]; done

  end.
