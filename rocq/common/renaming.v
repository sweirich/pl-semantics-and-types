Require Import ssreflect.
Require Import common.fintype.

Import CombineNotations.

Definition up_ren2 {m n} (δ : ren m n) := 
  (var_zero .: ((shift var_zero) .: (δ >> (shift >> shift)))).

(** A renaming transforms terms from context Γ to context Δ when the types
    declared in Γ are consistent with the types in Δ.

    The renaming operation generalizes "weakening" and "permutation"
    lemmas. The new context Δ can include new assumptions and the order of the
    variables in the context doesn't have to be the same.  *)
Definition typing_renaming {A}{n} (Δ : fin n -> A) {m} (δ : fin m -> fin n)
  (Γ : fin m -> A) : Prop := 
  forall x, Γ x = Δ (δ x).

(** The identity renaming preserves the context *)
Lemma typing_renaming_id {A}{n} (Δ : fin n -> A) :
  typing_renaming Δ id Δ.
Proof. unfold typing_renaming. intros x. done. Qed.

(** shift extends the context *)
Lemma typing_renaming_shift {A}{n} (Γ : fin n -> A) (τ : A) :
    typing_renaming (τ .: Γ) shift Γ.
Proof.
  unfold typing_renaming. intros x. fsimpl. done. Qed.

(** Extend a renaming with a new definition *)
Lemma typing_renaming_cons {A}{n} (Δ : fin n -> A) 
  {m} (Γ : fin m -> A) (δ : fin m -> fin n) (τ : A) (x : fin n) :
  typing_renaming Δ δ Γ ->
  typing_renaming Δ (x .: δ) ((Δ x) .: Γ).
Proof. intro h. unfold typing_renaming in *. auto_case (cbn;eauto). Qed.

(** Lift a renaming to a new scope *)
Lemma typing_renaming_lift {A}{n} (Δ : fin n -> A) 
  {m} (Γ : fin m -> A) (δ : fin m -> fin n) (τ : A) :
  typing_renaming Δ δ Γ ->
  typing_renaming (τ .: Δ) (up_ren δ) (τ .: Γ).
Proof. intro h. unfold typing_renaming in *. auto_case (cbn;eauto). Qed.

(** Lift a renaming to a new scope (twice) *)
Lemma typing_renaming_lift2 {A}{n} (Δ : fin n -> A) 
  {m} (Γ : fin m -> A) (δ : fin m -> fin n) (τ1 τ2 : A) :
  typing_renaming Δ δ Γ ->
  typing_renaming (scons τ1 (scons τ2 Δ)) (up_ren2 δ) (scons τ1 (scons τ2 Γ)).
Proof. intro h. unfold typing_renaming in *. auto_case (cbn;eauto). Qed.


Create HintDb renaming.
#[export] Hint Resolve typing_renaming_lift typing_renaming_cons
  typing_renaming_lift2 typing_renaming_id typing_renaming_shift : renaming.


Module Type LANG.

Parameter Ty : Type.
Definition Ctx := fun n => fin n -> Ty.
Parameter Tm : nat -> Type.
Parameter var : forall n, fin n -> Tm n.
Arguments var {_}.
Parameter typing : forall n, Ctx n -> Tm n -> Ty -> Prop.
Arguments typing {_}.
Parameter t_var : forall n Γ (x : fin n), typing Γ (var x) (Γ x). 
Parameter ren_Tm : forall m n, ren m n -> Tm m -> Tm n.
Arguments ren_Tm {_}{_}.

Definition up_Tm_Tm {m n} (sigma : fin m -> Tm n) :
  fin (S m) -> Tm (S n).
Proof.
  exact (scons (var var_zero) (core.funcomp (ren_Tm shift) sigma)).
Defined.

Parameter renaming_tm : forall {n} (Γ : Ctx n) e τ {m} (Δ:Ctx m) δ ,
  typing Γ e τ -> typing_renaming Δ δ Γ -> typing Δ (ren_Tm δ e) τ.
End LANG.

Module Substitution (L : LANG).
Import L.

Definition typing_subst {n} (Δ : fin n -> Ty) {m} (σ : fin m -> Tm n)
  (Γ : fin m -> Ty) : Prop := 
  forall x, typing Δ (σ x) (Γ x).

(** The empty substitution closes the term *)
Lemma typing_subst_null {n} (Δ : Ctx n) :
  typing_subst Δ null null.
Proof. unfold typing_subst. auto_case(cbn; eauto). Qed.

(** The identity substitution preserves the context *)
Lemma typing_subst_id {n} (Δ : Ctx n) :
  typing_subst Δ var Δ.
Proof. unfold typing_subst. intro x. eapply t_var. Qed.

Lemma typing_subst_cons {n} (Δ : Ctx n) {m} (σ : fin m -> Tm n)
  (Γ : Ctx m) e τ : 
 typing Δ e τ ->
 typing_subst Δ σ Γ ->
 typing_subst Δ (e .: σ) (τ .: Γ).
Proof.
  intros tE tS.
  unfold typing_subst in *.
  intro x. destruct x as [y|].
  fsimpl. eauto.
  fsimpl. eauto.
Qed.

Lemma typing_subst_lift {n} (Δ : Ctx n) {m} (σ : fin m -> Tm n)
  (Γ : Ctx m) τ : 
  typing_subst Δ σ Γ ->
  typing_subst (τ .: Δ) (up_Tm_Tm σ) (τ .: Γ).
Proof.
  unfold typing_subst in *.
  intros h.
  auto_case (fsimpl; cbn; eauto).
  + unfold core.funcomp.
    eapply renaming_tm; eauto. 
    unfold typing_renaming. fsimpl. done.
  + eapply t_var.
Qed.

End Substitution.

