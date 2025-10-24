From Stdlib Require Import Arith.
From Stdlib Require Import Psatz.

Require Export time.typesyntax.
Disable Notation "↑__Ty" (all).

Require Export time.eff.

Require Export rec.reduction.
Import rec.reduction.Notations.

Import time.eff.Notations.


(** * Type and effect relation *)

Definition allows_rec_ty (ty : Ty 0) := 
  match ty with 
  | Arr _ None _ => true
  | Prod None _ _ => true
  | _ => false
  end.

Definition Ctx (n : nat) := fin n -> Ty 0.

Inductive typing_val {n} (Γ : Ctx n) : Val n -> Ty 0 -> Prop := 
  | t_var x : 
    typing_val Γ (var x) (Γ x)

  | t_zero : 
    typing_val Γ zero Nat

  | t_succ k : 
    typing_val Γ k Nat ->
    typing_val Γ (succ k) Nat

  | t_prod v1 v2 τ1 τ2 ϕ : 
    typing_val Γ v1 τ1 ->
    typing_val Γ v2 τ2 -> 
    typing_val Γ (prod v1 v2) (Prod ϕ τ1 τ2)

  | t_inl v τ1 τ2 : 
    typing_val Γ v τ1 ->
    typing_val Γ (inj true v) (Sum τ1 τ2)

  | t_inr v τ1 τ2 : 
    typing_val Γ v τ2 ->
    typing_val Γ (inj false v) (Sum τ1 τ2)

  | t_abs e τ1 τ2 ϕ : 
    typing (τ1 .: Γ) e τ2 ϕ -> 
    typing_val Γ (abs e) (Arr τ1 ϕ τ2)

  | t_rec v τ : 
    allows_rec_ty τ = true ->
    typing_val (τ .: Γ) v τ -> 
    typing_val Γ (rec v) τ

  | t_fold v τ : 
    typing_val Γ v (τ [(Mu τ) ..]) ->
    typing_val Γ (fold v) (Mu τ)

with typing {n} (Γ : Ctx n) : Tm n -> Ty 0 -> Eff -> Prop := 


 | t_unfold v τ : 
    typing_val Γ v (Mu τ) ->
    typing Γ (unfold v) (τ [(Mu τ) ..]) ⊤

 | t_sub e τ ϕ1 ϕ2 : 
    typing Γ e τ ϕ1 -> 
    ϕ1 <: ϕ2 ->
    typing Γ e τ ϕ2
.

Definition t_var' {n} (Γ : Ctx n) x τ   : Γ x = τ -> typing_val Γ (var x) τ.
intros <-. eapply t_var. Qed.

#[export] Hint Resolve t_var' : rec.

#[export] Hint Constructors typing_val typing : rec.

Module Notations.
Export reduction.Notations.
Notation "Γ |-v v ∈ τ" := (typing_val Γ v τ) (at level 70) : rec_scope.
Notation "Γ |-e e ∈ τ @ ϕ" := (typing Γ e τ ϕ) (at level 70) : rec_scope.
End Notations.


Open Scope rec_scope.
Import Notations.

(** * Renaming lemma *)

Fixpoint renaming_val {n} (Γ : Ctx n) v τ {m} (Δ:Ctx m) δ : 
  Γ |-v v ∈ τ -> typing_renaming Δ δ Γ -> Δ |-v v⟨δ⟩ ∈ τ
with renaming_tm {n} (Γ : Ctx n) e τ {m} (Δ:Ctx m) δ ϕ : 
  Γ |-e e ∈ τ @ ϕ -> typing_renaming Δ δ Γ -> Δ |-e e⟨δ⟩ ∈ τ @ ϕ.
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

(** * Substution lemmas *)

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
Qed.

(** Add the substitution lemmas as hints *)
#[export] Hint Resolve typing_subst_lift typing_subst_cons
             typing_subst_id typing_subst_null : rec.

Fixpoint substitution_val {n} (Γ : Ctx n) v τ {m} (Δ:Ctx m) σ : 
  Γ |-v v ∈ τ -> typing_subst Δ σ Γ -> Δ |-v v[σ] ∈ τ
with
  substitution_tm {n} (Γ : Ctx n) e τ {m} (Δ:Ctx m) σ ϕ : 
  Γ |-e e ∈ τ @ ϕ -> typing_subst Δ σ Γ -> Δ |-e e[σ] ∈ τ @ ϕ.
Proof.
  all: intros h tS.
  all: inversion h; subst.
  all: cbn; asimpl.
  all: try solve [econstructor; eauto with rec].
  - unfold typing_subst in tS. eauto.
Qed.

#[export] Hint Resolve substitution_val substitution_tm : rec.

(** * Type safety *)

Lemma ret_inversion n (Γ:Ctx n) v τ ϕ : 
  Γ |-e ret v ∈ τ @ ϕ -> Γ |-v v ∈ τ.
Proof.
  intro h. dependent induction h; eauto.
Qed.

(** The usual preservation lemma does not tell us much about 
   the computation. *)     
Lemma preservation e e' τ ϕ :
  null |-e e ∈ τ @ ϕ -> e ~> e' -> null |-e e' ∈ τ @ ϕ.
Proof. 
  intro h.
  move: e'.
  dependent induction h.
  all: intros e' S; inversion S; subst.
  all: try solve [eauto using t_sub, eff.bot_le, sub_incr with rec].
  all: try solve [inversion H; subst; 
                  eauto using t_sub, eff.bot_le, sub_incr with rec].
(* FILL IN HERE *) Admitted.



Ltac impossible_var := 
  match goal with | [ x : (fin 0) |- _ ] => destruct x end.


Lemma progress e τ ϕ :
  null |-e e ∈ τ @ ϕ -> (exists v, e = ret v) \/ (exists e', e ~> e').
Proof.
  intros h.
  dependent induction h.
  all: try solve [inversion H; subst; [impossible_var| done | ];
    right; eauto with rec].
(* FILL IN HERE *) Admitted.


(** If a term typechecks with a finite number of steps, then it 
    must terminate within that bound *)
Lemma finite_step_soundness k e τ : 
  null |-e e ∈ τ @ Some k -> 
        exists j, exists v, step_n Small.step j e (ret v) /\ j <= k.
Proof.
(* FILL IN HERE *) Admitted.
