From Stdlib Require Import Psatz.
From Stdlib Require Import Arith.
From Stdlib Require Import ssreflect.


(* Well-founded induction is part of Rocq's standard 
   library. We only need it for the natural numbers though
   so we define a specialized version here.

   Briefly, it says that we can prove a property about 
   all numbers by showing it for some number m, under the 
   assumption that it holds for all numbers less than m.

 *)
Lemma strong_ind (P : nat -> Prop) :
  (forall m, (forall k : nat, k < m -> P k) -> P m) -> forall n, P n.
Proof. intro h. induction n as [ n IHn ] using (well_founded_induction lt_wf). eauto. Qed.


(** We want to work with a class of propositions that 
    are indexed by steps and downward closed *)

Definition iProp := nat -> Prop.
Declare Scope iProp_scope.
Delimit Scope iProp_scope with I.
Bind Scope iProp_scope with iProp.
Open Scope iProp_scope.

Class IProp (ϕ : iProp) := 
  { dclosed : forall k, ϕ k -> forall j, j <= k -> ϕ j }.

(** Conjunction *)
Definition iAnd ϕ ψ : iProp := fun k => ϕ k /\ ψ k.

#[export] Instance IProp_iAnd {ϕ ψ} `{IProp ϕ}`{IProp ψ} : IProp (iAnd ϕ ψ).
constructor. intros k h. intros j LE. destruct h as [h1 h2].
split. eapply dclosed; eauto. eapply dclosed; eauto. Qed.

(** Disjunction *)
Definition iOr ϕ ψ : iProp := fun k => ϕ k \/ ψ k.

#[export] Instance IProp_iOr {ϕ ψ} `{IProp ϕ}`{IProp ψ} : IProp (iOr ϕ ψ).
constructor. intros k h. intros j LE. destruct h as [h1|h2].
left; eapply dclosed; eauto. right; eapply dclosed; eauto. Qed.


(* As we build sets, it is easy to lose the downward closure property, especially 
   in the presence of implication. The problem is that even if ϕ and ψ are downward 
   closed, the iProp  `fun k => ϕ k -> ψ k` is not. The problem is contravariance.  *)

(** Implication *)
Definition iImp ϕ ψ : iProp := (fun k => forall j, j <= k -> ϕ j -> ψ j).

#[export] Instance IProp_iImp {ϕ ψ : iProp} : IProp (iImp ϕ ψ).
constructor. intros k h j LEj i LEi hi. eapply h. 
lia. auto. Qed.

(** The Later modality *)
Definition iLater ϕ := 
  (fun k => match k with O => True | S j => ϕ j end).

#[export] Instance IProp_iLater {ϕ} `{IProp ϕ} : IProp (iLater ϕ).
Proof. split. intros k h j LE. destruct j. cbn. done.
  inversion LE. subst. cbn. eapply dclosed; eauto.
  subst. cbn. cbn in h. eapply dclosed; eauto. lia.
Qed.


Definition iExists {T} (ϕ : T -> iProp) : iProp := fun k => exists x, ϕ x k.

#[export] Instance IProp_iExists {T} {ϕ : T -> iProp}
  `{forall x, IProp (ϕ x)} : IProp (iExists ϕ).
Proof.
  constructor. intros k h j LE. 
  unfold iExists in h. unfold iExists.
  destruct h as [x h].
  exists x. eapply H; eauto.
Qed.


(* -------------------------------------------- *)

Module Notations.
Infix "⇒" := (iImp) (right associativity, at level 70) : iProp_scope.
Notation "▷ ϕ" := (iLater ϕ) (at level 10) : iProp_scope.
End Notations.
Import Notations.



Ltac next i := destruct i; cbn; first done.

Lemma later {ϕ} `{IProp ϕ} : forall k, ϕ k -> ▷ ϕ k.
intros k. destruct k; cbn. done. intro h. eapply dclosed; eauto. Qed.
Lemma lift {ϕ ψ} : (forall k, ϕ k -> ψ k) -> forall k, ▷ ϕ k -> ▷ ψ k.
Proof. intros h k m. next k. eauto. Qed.

Lemma loeb_induction ϕ : (forall k, ▷ ϕ k -> ϕ k) -> forall k, ϕ k.
Proof.
  intros ih.
  move=> k. 
  eapply strong_ind. clear k. intros k IHS.
  eapply ih.
  destruct k. cbn. done.
  cbn. eapply IHS. done.
Qed.
