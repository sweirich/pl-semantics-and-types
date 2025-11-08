(** The rec programming language extended with only exceptions, plus
    a type-and-effect system for statically tracking exceptions. *)

(** * Imports *)

(** Type soundness for control operators *)

From Stdlib Require Export ssreflect.
From Stdlib Require Export Program.Equality.
Require Export common.core.
Require Export common.fintype.

Require Export common.fin_util.
Require Export common.relations.
Require Export common.renaming.

(** Effects a sets of potentially raised exceptions *)
Require Export exn.eff.

(** The syntax file defines notations for printing. However, this syntax can 
    sometimes be confusing so we disable it here. *)
Require Export exn.syntax.
Disable Notation "↑__Val" (all).
Disable Notation "↑__Tm" (all).
Disable Notation "'__Val'" (all).

Import eff.Notations.

(** For simplicity, we are skipping recursive types and values *)
Inductive Ty : Type :=
  | Unit : Ty
  | Void : Ty
  | Nat : Ty
  | Prod : Ty -> Ty -> Ty
  | Sum : Ty -> Ty -> Ty
  | Arr : Ty -> Eff -> Ty -> Ty
  | Exn : Ty.

(** Define a notation scope specific to this language. *)
Declare Scope rec_scope.

Module SyntaxNotations.
Export ScopedNotations.
Notation "'prj1'" := (prj true) (at level 70) : rec_scope.
Notation "'prj2'" := (prj false) (at level 70) : rec_scope.
Notation "'inj1'" := (inj true) (at level 70) : rec_scope.
Notation "'inj2'" := (inj false) (at level 70) : rec_scope.
Notation "⇑" := (up_Val_Val) : rec_scope.
Notation "⇑ σ" := (var var_zero .: σ >> ren_Val ↑) 
                    (only printing, at level 0) : rec_scope.
End SyntaxNotations.

Open Scope rec_scope.
Open Scope list_scope.
Export SyntaxNotations.

(** * Syntax properties *)

(** Decide whether a value is a natural number value *)
Fixpoint is_nat (v : Val 0) : bool := 
  match v with 
  | zero => true
  | succ v1 => is_nat v1 
  | _ => false
  end.

(** * Primitive reductions (i.e. beta steps) 
  
  Because we've defined a new syntax for this language, we have to redefine
  these operations here. But they are the same as they were before.
*)

Reserved Notation "e ~>> e'" (at level 70) .

Inductive primitive : Tm 0 -> Tm 0 -> Prop := 
  | s_beta : forall (e : Tm 1) (v : Val 0), 
      app (abs e) v ~>> e[v..]
  | s_ifz_zero : forall (e1 : Tm 0) (e2 : Tm 1), 
      ifz zero e1 e2 ~>> e1
  | s_ifz_succ : forall (e1 : Tm 0) (e2 : Tm 1) (k : Val 0), 
      ifz (succ k) e1 e2 ~>> e2[k..]
  | s_prj1 : forall v1 v2 : Val 0, 
      prj1 (prod v1 v2) ~>> ret v1
  | s_prj2 : forall v1 v2 : Val 0, 
      prj2 (prod v1 v2) ~>> ret v2
  | s_case_inj1 : forall (v : Val 0) (e1 e2 : Tm 1), 
      case (inj1 v) e1 e2 ~>> e1[v..]
  | s_case_inj2 : forall (v : Val 0) (e1 e2 : Tm 1), 
      case (inj2 v) e1 e2 ~>> e2[v..]
where "e ~>> e'" := (primitive e e').

Lemma primitive_deterministic :
  forall e e1 e2, e ~>> e1 -> e ~>> e2 -> e1 = e2.
Proof.
  intros e e1 e2 h1 h2.
  inversion h1; subst; inversion h2; subst; eauto.
Qed.


(** * Semantics based on an abstract machine with an explicit stack *)

(** The frames that we care about are always closed *)
Definition frame : Type := Frame 0.

(** A stack is a list of frames. *)
Definition Stack n := list (Frame n).
Definition stack := list (Frame 0).

(** A machine state is the current expression that we are evaluated, paired 
    with a control stack. *)
Definition machine : Type := (stack * Tm 0).

(** The machine is done evaluating when the stack is empty and 
    the expression is a value. *)
Inductive final : machine -> Prop := 
  | final_eval v :
    final (nil, ret v)
  | final_exn v :
    final (nil, raise v).

Module Stack.

(** Exceptions: Search for a 'try' frame on the stack for a raised exception 'x' *)
Fixpoint find_exn (s : stack) (x : nat) : machine := 
  match s with 
  (* we found a try block, check if it applies to this exn *)
  | cons (f_try y e2) k => 
      if PeanoNat.Nat.eqb x y then (k, e2) else find_exn k x
  (* no handler, keep looking *)
  | cons _ k  => find_exn k x
  (* uncaught exception *)
  | nil => (nil, raise (exn x)) 
  end.


Inductive step : machine -> machine -> Prop := 
  | s_prim s e e' : 
    e ~>> e' ->
    step (s, e) (s, e')

  | s_pop s e2 v : 
    step (f_let e2 :: s, ret v) (s, e2[v..])

  | s_push s e1 e2 : 
    step (s, let_ e1 e2) (f_let e2 :: s, e1)

  (** exceptions *)
  (* raise an exception *)
  | s_raise f s x : 
    step (f :: s, raise (exn x)) (find_exn (cons f s) x) 

  (* install (push) an exception handler *)
  | s_try s e1 x e2 : 
    step (s, try e1 x e2) (f_try x e2 :: s, e1)

  (* discard (pop) an exception hander *)
  | s_discard_try s x e2 v : 
    step (f_try x e2 :: s, ret v) (s,ret v)
.
  
Definition irreducible (m : machine) : Prop := 
  forall m', not (step m m').

Lemma deterministic :
  forall m m1 m2, step m m1 -> step m m2 -> m1 = m2.
Proof.
  intros m m1 m2 h1 h2. 
  inversion h1; subst; inversion h2; subst; auto.
  all : try solve [ match goal with [ H : _ _ ~>> _ |- _ ] => inversion H end ].
  eapply primitive_deterministic in H; eauto. subst. auto.
Qed.

End Stack.

(** * Typing relation *)

Definition Ctx (n : nat) := fin n -> Ty.

Inductive typing_val  {n} (Γ : Ctx n) : Val n -> Ty -> Prop := 
  | t_unit : 
    typing_val Γ unit Unit 

  | t_var x : 
    typing_val Γ (var x) (Γ x)

  | t_zero : 
    typing_val Γ zero Nat

  | t_succ k :
    typing_val Γ k Nat -> 
    typing_val Γ (succ k) Nat

  | t_prod v1 v2 τ1 τ2 : 
    typing_val Γ v1 τ1 ->
    typing_val Γ v2 τ2 -> 
    typing_val Γ (prod v1 v2) (Prod τ1 τ2)

  | t_inl v τ1 τ2 : 
    typing_val Γ v τ1 ->
    typing_val Γ (inj true v) (Sum τ1 τ2)

  | t_inr v τ1 τ2 : 
    typing_val Γ v τ2 ->
    typing_val Γ (inj false v) (Sum τ1 τ2)

  | t_abs e τ1 τ2 ϕ : 
    typing (τ1 .: Γ) e τ2 ϕ ->
    typing_val Γ (abs e) (Arr τ1 ϕ τ2)

  | t_exn k : 
    typing_val Γ (exn k) Exn

with typing {n} (Γ : Ctx n) : Tm n -> Ty -> Eff -> Prop := 
  | t_ret v τ :
    typing_val Γ v τ ->
    typing Γ (ret v) τ ⊥

  | t_let e1 e2 τ1 τ2 ϕ1 ϕ2 :
    typing Γ e1 τ1 ϕ1 ->
    typing (τ1 .: Γ) e2 τ2 ϕ2 ->
    typing Γ (let_ e1 e2) τ2 (ϕ1 ⊕ ϕ2)

  | t_app v1 v2 τ1 τ2 ϕ : 
    typing_val Γ v1 (Arr τ1 ϕ τ2) -> 
    typing_val Γ v2 τ1 -> 
    typing Γ (app v1 v2) τ2 ϕ

  | t_ifz v e0 e1 τ ϕ :
    typing_val Γ v Nat -> 
    typing Γ e0 τ ϕ  -> 
    typing (Nat .: Γ) e1 τ ϕ -> 
    typing Γ (ifz v e0 e1) τ ϕ

  | t_prj1 v τ1 τ2 :
    typing_val Γ v (Prod τ1 τ2) -> 
    typing Γ (prj1 v) τ1 ⊥

  | t_prj2 v τ1 τ2 :
    typing_val Γ v (Prod τ1 τ2) -> 
    typing Γ (prj2 v) τ2 ⊥

  | t_case v e1 e2 τ1 τ2 τ ϕ : 
    typing_val Γ v (Sum τ1 τ2) ->
    typing (τ1 .: Γ) e1 τ ϕ ->
    typing (τ2 .: Γ) e2 τ ϕ ->
    typing Γ (case v e1 e2) τ ϕ

  | t_sub e τ ε1 ε2 : 
    typing Γ e τ ε1 -> 
    ε1 <: ε2 ->
    typing Γ e τ ε2
  
  (** exceptions *)
  | t_raise τ x : 
    typing Γ (raise (exn x)) τ (singleton x)

  | t_try e1 x e2 τ ϕ : 
    typing Γ e1 τ (ϕ ⊕ (singleton x)) ->
    typing Γ e2 τ ϕ ->
    typing Γ (try e1 x e2) τ ϕ
.

(* TODO: define a typing judgement for stacks, frames, and machines *)

Inductive typing_frame {n} (Γ : Ctx n) : Frame n -> Ty -> Eff -> Ty -> Eff -> Prop :=
.

Inductive typing_stack {n} (Γ : Ctx n) : 
  Stack n -> Ty -> Eff -> Ty -> Eff -> Prop :=
.


Inductive machine_ok : machine -> Eff -> Prop := 
.

(* NOTE: Your machine_ok judgement should allow subeffecting. *)
Lemma m_sub m ϕ1 ϕ2 : machine_ok m ϕ1 -> ϕ1 <: ϕ2 -> machine_ok m ϕ2.
Proof. (* FILL IN HERE *) Admitted.

(** This version of t_var is easier to work with sometimes
    as it doesn't require the type to already be in the form 
    Γ x. *)
Definition t_var' {n} (Γ : Ctx n) x τ   : Γ x = τ -> typing_val Γ (var x) τ.
intros <-. eapply t_var. Qed.

#[export] Hint Resolve t_var' : rec.

#[export] Hint Constructors typing_val typing 
  typing_frame typing_stack machine_ok : rec.


(** * Notation *)

Module Notations.
Infix "↦"  := Stack.step (at level 70) : rec_scope.
Infix "↦*"  := (multi Stack.step) (at level 70) : rec_scope.
Notation "Γ |-v v ∈ τ" := (typing_val Γ v τ) (at level 70) : rec_scope.
Notation "Γ |-e e ∈ τ @ ϕ" := (typing Γ e τ ϕ) (at level 70) : rec_scope.
Notation "Γ |-f f ∈ τ1 @ ϕ1 ~> τ2 @ ϕ2" := (typing_frame Γ f τ1 ϕ1 τ2 ϕ2) (at level 70): rec_scope.
Notation "Γ |-s s ∈ τ1 @ ϕ1 ~> τ2 @ ϕ2" := (typing_stack Γ s τ1 ϕ1 τ2 ϕ2) (at level 70) : rec_scope.
End Notations.

Import Notations.


(** * Inversion Lemmas *)

(* Because the typing rule for terms is not syntax-directed (due to
 sub-effecting), we need inversion lemmas to invert the judgement. *)

Lemma invert_ret {n} (Γ:Ctx n) v τ ε : 
  Γ |-e ret v ∈ τ @ ε -> Γ |-v v ∈ τ.
Proof.
  intro h. dependent induction h; eauto.
Qed.

Lemma invert_let {n} (Γ : Ctx n) e1 e2 τ ϕ :
   Γ |-e let_ e1 e2 ∈ τ @ ϕ -> 
   exists τ1 ϕ1 ϕ2, 
      Γ |-e e1 ∈ τ1 @ ϕ1 /\
      τ1 .: Γ |-e e2 ∈ τ @ ϕ2 /\
      (ϕ1 ⊕ ϕ2) <: ϕ.
Proof.
  intro h.
  dependent induction h.
  - repeat eexists; eauto. reflexivity.
  - edestruct IHh as [τ1 [ϕ1 [ϕ2 [h1 [h2 h3]]]]]; eauto.
    repeat eexists; eauto. 
    effdec.
Qed.

Lemma invert_raise {n} (Γ : Ctx n) x τ ϕ : 
  Γ |-e raise (exn x) ∈ τ @ ϕ -> singleton x <: ϕ.
Proof. 
  intro h. dependent induction h.
  specialize (IHh _ ltac:(auto)). effdec.
  effdec.
Qed.

Lemma invert_try {n} (Γ : Ctx n) e1 x e2 τ ϕ : 
  Γ |-e try e1 x e2 ∈ τ @ ϕ -> 
  Γ |-e e1 ∈ τ @ (ϕ ⊕ singleton x) /\ Γ |-e e2 ∈ τ @ ϕ.
Proof.
  intro h.
  dependent induction h.
  - edestruct IHh; eauto. 
    split; eapply t_sub; eauto. effdec.
  - split; eauto.
Qed.

(** A tactic to invert typing hypotheses in the context, when the 
    syntax of the value/term/stack/frame is not a variable.
 Automatically applies the inversion lemmas from above. *)
Ltac invert_typing := 
  match goal with 
    | [ H : typing_val _ (_ _) _ |- _ ] => 
        inversion H; subst; clear H
    | [ H : typing_stack _ (cons _ _) _ _ _ _ |- _ ] => 
        inversion H; subst; clear H
    | [ H : typing _ (ret _) _ _  |- _ ] =>
        apply invert_ret in H; eauto
    | [ H : typing _ (raise _) _ _  |- _ ] =>
        eapply invert_raise in H; eauto
    | [ H : typing _ (try _ _ _) _ _  |- _ ] =>
        eapply invert_try in H; eauto; destruct H
    | [ H : typing _ (let_ _ _) _ _ |- _ ] => 
        eapply invert_let in H; eauto;
           destruct H as [? [? [? [? [? ?]]]]]
    | [ H : typing_frame _ (_ _) _ _ _ _ |- _ ] => 
        inversion H; subst; clear H
    end.


(** * Basic properties of the typing relation *)


(** Renaming lemma *)

Fixpoint renaming_val {n} (Γ : Ctx n) v τ {m} (Δ:Ctx m) δ : 
  Γ |-v v ∈ τ -> typing_renaming Δ δ Γ -> Δ |-v v⟨δ⟩ ∈ τ
with renaming_tm {n} (Γ : Ctx n) e τ ϕ {m} (Δ:Ctx m) δ : 
  Γ |-e e ∈ τ @ ϕ -> typing_renaming Δ δ Γ -> (Δ |-e e⟨δ⟩ ∈ τ @ ϕ).
Proof. 
  - intros h tR; inversion h.
    all: asimpl.
    all: try solve [econstructor; eauto with renaming].
    + (* var case *)
      eapply t_var'; eauto. 
  - intros h tR; inversion h.
    all: asimpl.
    all: try solve [econstructor; eauto with renaming].
Qed.

Hint Resolve renaming_val renaming_tm : rec.

(** Substution lemmas *)

Definition typing_subst {n} (Δ : Ctx n) {m} (σ : fin m -> Val n)
  (Γ : Ctx m) : Prop := 
  forall x, (Δ |-v (σ x) ∈ (Γ x)).

Lemma typing_subst_null {n} (Δ : Ctx n) :
  typing_subst Δ null null.
Proof. unfold typing_subst. auto_case. Qed.

Lemma typing_subst_id {n} (Δ : Ctx n) :
  typing_subst Δ var Δ.
Proof. unfold typing_subst. intro x. econstructor. Qed.

Lemma typing_subst_cons {n} (Δ : Ctx n) {m} (σ : fin m -> Val n)
  (Γ : Ctx m) v τ : 
 Δ |-v v ∈ τ -> typing_subst Δ σ Γ ->
 typing_subst Δ (v .: σ) (τ .: Γ).
Proof. intros. unfold typing_subst in *. intros [y|]; asimpl; eauto. Qed.

Lemma typing_subst_lift {n} (Δ : Ctx n) {m} (σ : fin m -> Val n)
  (Γ : Ctx m) τ : 
  typing_subst Δ σ Γ -> typing_subst (τ .: Δ) (⇑ σ) (τ .: Γ).
Proof.
  unfold typing_subst in *.
  intros h. auto_case; eauto with renaming rec. 
  unfold funcomp.
  eapply renaming_val; eauto.
  eapply typing_renaming_shift.
Qed.

(** Add the substitution lemmas as hints *)
#[export] Hint Resolve typing_subst_lift typing_subst_cons
             typing_subst_id typing_subst_null : rec.

Fixpoint substitution_val {n} (Γ : Ctx n) v τ {m} (Δ:Ctx m) σ : 
  Γ |-v v ∈ τ -> typing_subst Δ σ Γ -> Δ |-v v[σ] ∈ τ
with
  substitution_tm {n} (Γ : Ctx n) e τ {m} (Δ:Ctx m) σ ϕ: 
  Γ |-e e ∈ τ @ ϕ -> typing_subst Δ σ Γ -> Δ |-e e[σ] ∈ τ @ ϕ.
Proof.
  all: intros h tS.
  all: inversion h; subst.
  all: cbn.
  all: try solve [econstructor; eauto with rec].
  - unfold typing_subst in tS. eauto.
Qed.

#[export] Hint Resolve substitution_val substitution_tm : rec.


(** * Preservation lemma *)


Lemma primitive_preservation e e' τ ϕ:
  (null |-e e ∈ τ @ ϕ) -> e ~>> e' ->  null |-e e' ∈ τ @ ϕ.
Proof.
  intro h. 
  move: e'.
  dependent induction h.
  all: intros e' S; inversion S; subst.
  all: try solve [eauto with rec].
  all: try solve [inversion H; subst; eauto with rec].
Qed. 


(** The [preservation_find_exn] lemma proves that the [find_exn s k] operation 
    produces a well-formed next state by searching the stack for an exception 
    handler for k.

    Your homework is to state and prove this lemma.
    
    Your version of this lemma should calculate what the effects of that 
    new machine will be.

    If you would like to attempt to prove this lemma correct in Rocq, you will
    need to use [PeanoNat.Nat.eqb] and [PeanoNat.Nat.eqb_neq]. 

    Furthermore the [effdec] tactic will be very useful.
 *)



(** You should use the preservation_find_exn lemma in the case for s_raise *)
Lemma machine_preservation m m' ϕ : 
  machine_ok m ϕ -> 
  Stack.step m m' -> machine_ok m' ϕ.
Proof. 
  intros h hS.
  (* invert step *)
  inversion hS; subst; clear hS.
(* FILL IN HERE *) Admitted.

(** progress *)

(** [canonical_value] is a tactic to invert the value typing, when the type is
not a meta-variable. This acts like a canonical forms lemma.  NOTE: we have a
separate tactic for Nats because they are the only inductively-defined
values. We need to be careful about how we invert them as they produce 
new values.
 *)
Ltac canonical_value := 
  lazymatch goal with 
    | [ H : typing_val null _ (Arr _ _ _) |- _ ] => inversion H; subst; clear H
    | [ H : typing_val null _ Exn |- _ ] => inversion H; subst; clear H
    | [ H : typing_val null _ (Prod _ _) |- _ ] => inversion H; subst; clear H
    | [ H : typing_val null _ (Sum _ _) |- _ ] => inversion H; subst; clear H
  end;
  try match goal with [ x : fin 0 |- _ ] => destruct x end;
  try done.

Ltac canonical_Nat := 
  match goal with 
    | [ H : typing_val null _ Nat   |- _ ] => inversion H; subst; clear H
  end;
  try match goal with [ x : fin 0 |- _ ] => destruct x end;
  try done.

Ltac is_reducible := 
  match goal with [ IR : Stack.irreducible _ |- _ ] => 
      assert False; [eapply IR; eauto using Stack.step, primitive|]; done end.

(** Well-formed machines either reduce or in a designated final configuration 
    We prove this "A or B" statement in an equivalent form as "not A implies B".
*)
Lemma machine_progress m ϕ : machine_ok m ϕ -> Stack.irreducible m -> final m.
Proof. 
  intros h IR. 
  (* FILL IN HERE *) Admitted.


