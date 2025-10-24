Require Export div.typesyntax.
Disable Notation "↑__Ty" (all).

Require Export rec.reduction.
Import rec.reduction.Notations.

Import eff.Notations.

(** Type and effect relation *)

Definition allows_rec_ty (ty : Ty 0) := 
  match ty with 
  | Arr _ ⊤ _ => true
  | Prod ⊤ _ _ => true
  | _ => false
  end.

Definition Ctx (n : nat) := fin n -> Ty 0.

(* ---------------------------------------------------------- *)

Inductive typing_val {n} (Γ : Ctx n) : Val n -> Ty 0 -> Prop := 
  | t_var x : 
    typing_val Γ (var x) (Γ x)

  | t_zero : 
    typing_val Γ zero Nat

  | t_succ k : 
    typing_val Γ k Nat ->
    typing_val Γ (succ k) Nat

  (* We don't have subtyping, so to provide flexibility
     we allow ε to be anything *)
  | t_prod v1 v2 τ1 τ2 ε : 
    typing_val Γ v1 τ1 ->
    typing_val Γ v2 τ2 -> 
    typing_val Γ (prod v1 v2) (Prod ε τ1 τ2)

  | t_inl v τ1 τ2 : 
    typing_val Γ v τ1 ->
    typing_val Γ (inj true v) (Sum τ1 τ2)

  | t_inr v τ1 τ2 : 
    typing_val Γ v τ2 ->
    typing_val Γ (inj false v) (Sum τ1 τ2)

  (* We can use t_sub to make ε anything *)
  | t_abs e τ1 τ2 ε : 
    typing (τ1 .: Γ) e τ2 ε ->
    typing_val Γ (abs e) (Arr τ1 ε τ2)

  | t_rec v τ : 
    allows_rec_ty τ = true ->
    typing_val (τ .: Γ) v τ -> 
    typing_val Γ (rec v) τ

  | t_fold v τ : 
    typing_val Γ v (τ [(Mu τ) ..]) ->
    typing_val Γ (fold v) (Mu τ)

with typing {n} (Γ : Ctx n) : Tm n -> Ty 0 -> Eff -> Prop := 
  | t_ret v τ :
    typing_val Γ v τ ->
    typing Γ (ret v) τ ⊥

  | t_let e1 e2 τ1 τ2 ε1 ε2 :
    typing Γ e1 τ1 ε1 ->
    typing (τ1 .: Γ) e2 τ2 ε2 ->
    typing Γ (let_ e1 e2) τ2 (ε1 ⊕ ε2)

  | t_app v1 v2 τ1 τ2 ε1 : 
    typing_val Γ v1 (Arr τ1 ε1 τ2) -> 
    typing_val Γ v2 τ1 -> 
    typing Γ (app v1 v2) τ2 ε1

  | t_ifz v e0 e1 τ ε :
    typing_val Γ v Nat -> 
    typing Γ e0 τ ε -> 
    typing (Nat .: Γ) e1 τ ε -> 
    typing Γ (ifz v e0 e1) τ ε

  | t_prj1 v τ1 τ2 ε :
    typing_val Γ v (Prod ε τ1 τ2) -> 
    typing Γ (prj1 v) τ1 ε

  | t_prj2 v τ1 τ2 ε  :
    typing_val Γ v (Prod ε τ1 τ2) -> 
    typing Γ (prj2 v) τ2 ε

  | t_case v e1 e2 τ1 τ2 τ ε : 
    typing_val Γ v (Sum τ1 τ2) ->
    typing (τ1 .: Γ) e1 τ ε ->
    typing (τ2 .: Γ) e2 τ ε ->
    typing Γ (case v e1 e2) τ ε

 | t_unfold v τ : 
    typing_val Γ v (Mu τ) ->
    typing Γ (unfold v) (τ [(Mu τ) ..]) ⊤

 | t_sub e τ ε1 ε2 : 
    typing Γ e τ ε1 -> 
    ε1 <: ε2 ->
    typing Γ e τ ε2
.

Definition t_var' {n} (Γ : Ctx n) x τ   : Γ x = τ -> typing_val Γ (var x) τ.
intros <-. eapply t_var. Qed.

#[export] Hint Resolve t_var' : rec.

#[export] Hint Constructors typing_val typing : rec.

Module Notations.
Export reduction.Notations.
Notation "Γ |-v v ∈ τ" := (typing_val Γ v τ) (at level 70) : rec_scope.
Notation "Γ |-e e ∈ τ @ ε" := (typing Γ e τ ε) (at level 70) : rec_scope.
End Notations.

Ltac impossible_var := 
  match goal with | [ x : (fin 0) |- _ ] => destruct x end.

Open Scope rec_scope.
Import Notations.


(** * Renaming lemma *)

Fixpoint renaming_val {n} (Γ : Ctx n) v τ {m} (Δ:Ctx m) δ : 
  Γ |-v v ∈ τ -> typing_renaming Δ δ Γ -> Δ |-v v⟨δ⟩ ∈ τ
with renaming_tm {n} (Γ : Ctx n) e τ {m} (Δ:Ctx m) δ ε : 
  Γ |-e e ∈ τ @ ε -> typing_renaming Δ δ Γ -> Δ |-e e⟨δ⟩ ∈ τ @ ε.
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
  substitution_tm {n} (Γ : Ctx n) e τ {m} (Δ:Ctx m) σ ε : 
  Γ |-e e ∈ τ @ ε -> typing_subst Δ σ Γ -> Δ |-e e[σ] ∈ τ @ ε.
Proof.
  all: intros h tS.
  all: inversion h; subst.
  all: cbn; asimpl.
  all: try solve [econstructor; eauto with rec].
  - unfold typing_subst in tS. eauto.
Qed.

#[export] Hint Resolve substitution_val substitution_tm : rec.

(** * Type safety *)

Lemma ret_inversion n (Γ:Ctx n) v τ ε : 
  Γ |-e ret v ∈ τ @ ε -> Γ |-v v ∈ τ.
Proof.
  intro h. dependent induction h; eauto.
Qed.

Lemma preservation e e' τ ε :
  null |-e e ∈ τ @ ε -> e ~> e' -> null |-e e' ∈ τ @ ε.
Proof. 
  intro h.
  move: e'.
  dependent induction h.
  all: intros e' S; inversion S; subst.
  all: try solve [eauto using t_sub with rec].
  all: try solve [inversion H; subst; eauto using t_sub with rec].
(* FILL IN HERE *) Admitted.

Lemma progress e τ ε :
  null |-e e ∈ τ @ ε -> (exists v, e = ret v) \/ (exists e', e ~> e').
Proof.
  intros h.
  dependent induction h.
  all: try solve [inversion H; subst; [impossible_var | done | ];
    right; eauto with rec].
  - (* ret *) 
    left. eauto. 
  - (* let_ *)
    edestruct (IHh1 e1) as [[v ->]|[e' S]]; eauto.
    right. eauto with rec.
    right. eauto with rec.
(* FILL IN HERE *) Admitted.


(** * Semantic Soundness with effects *)

Definition C' V (τ : Ty 0) ε : Tm 0 -> Prop := 
  match ε with 
  | Bot => fun e => exists v, e ~>* ret v /\ V τ v
  | Top => fun e => True
  end.

Fixpoint V (τ : Ty 0) {struct τ} : Val 0 -> Prop := 
  match τ with 
  | Void => fun v => False
  | Nat => fun v => is_nat v = true
  | Arr τ1 ε τ2 => 
      fun v => 
        forall w, V τ1 w -> C' V τ2 ε (app v w)
  | Prod ε τ1 τ2 => 
      fun v => C' V τ1 ε (prj1 v) /\ C' V τ2 ε (prj2 v)
  | Sum τ1 τ2 => 
      fun v => (exists v1, v = inj true v1 /\ V τ1 v1) \/
            (exists v2, v = inj false v2 /\ V τ2 v2)

  | Mu τ => 
      fun v => exists v1, v = fold v1
  | _ => fun v => False
  end.

Definition C := C' V.

Lemma reverse_evaluation e e' τ ε :
  e ~> e' -> C τ ε e' -> C τ ε e .
Proof. 
  intros h. destruct ε; cbn. done. 
  intros [v [S Vv]]. 
  exists v. split. eapply ms_trans; eauto. auto.
Qed.

Definition Env n := fin n -> Val 0.

Definition semantic_subst {n} (Γ : Ctx n) (ρ : Env n) := 
  forall x, V (Γ x) (ρ x).

Definition semantic_typing {n} (Γ : Ctx n) e τ ε :=
  forall ρ, semantic_subst Γ ρ -> C τ ε e[ρ].

Module SoundnessNotation.
Notation "V⟦ τ ⟧" := (V τ).
Notation "C⟦ τ @ ε ⟧" := (C τ ε).
Notation "⟦ Γ ⟧" := (semantic_subst Γ). 
Notation "Γ ⊨v v ∈ τ" := (forall ρ, ⟦ Γ ⟧ ρ -> V τ v[ρ]) (at level 70).
Notation "Γ ⊨ e ∈ τ @ ε" := (forall ρ, ⟦ Γ ⟧ ρ -> C τ ε e[ρ]) (at level 70).
End SoundnessNotation.

Import SoundnessNotation.

Lemma semantic_subst_cons {τ v} {n} {Γ : Ctx n} {ρ} : 
  V⟦ τ ⟧ v ->  ⟦ Γ ⟧ ρ ->   ⟦ τ .: Γ ⟧ (v .: ρ).
Proof. unfold semantic_subst. intros Vv h. auto_case. Qed.


Lemma C_sub τ ε1 ε2 e : ε1 <: ε2 -> C⟦ τ @ ε1 ⟧ e -> C⟦ τ @ ε2 ⟧ e.
Proof.
  intros h hC.
  destruct ε1; destruct ε2; auto.
  cbn in h. done.
Qed.

Section Semtyping.
Context {n : nat} (Γ : Ctx n).

Lemma ST_var x : 
  Γ ⊨v var x ∈ Γ x.
Proof. 
  intros ρ ρH.
  specialize (ρH x). 
  asimpl.
  eauto.
Qed.

Lemma ST_abs (e : Tm (S n)) τ1 τ2 ε : 
  (τ1 .: Γ) ⊨ e ∈ τ2 @ ε -> 
  Γ ⊨v (abs e) ∈ Arr τ1 ε τ2.
Proof.
  intros IH.
  intros ρ ρH.
  cbn. destruct ε. 
  - cbn. eauto.
  - intros w wIn.
    move: (IH (w .: ρ)) => CH. 
    eapply reverse_evaluation.
    eapply Small.s_beta.
    asimpl.
    eapply CH. eapply semantic_subst_cons; eauto.
Qed.

Lemma ST_app v1 v2 τ1 ε1 τ2 : 
  Γ ⊨v v1 ∈ Arr τ1 ε1 τ2 -> 
  Γ ⊨v v2 ∈ τ1 -> 
  Γ ⊨ app v1 v2 ∈ τ2 @ ε1 .
Proof.
  intros h1 h2 ρ ρh.
  specialize (h1 ρ ρh). 
  specialize (h2 ρ ρh). 
  cbn in h1.
  destruct ε1.
  - cbn. done.
  - cbn.
    eapply h1; eauto.
Qed.

Lemma ST_zero {k:nat} :
   Γ ⊨v zero ∈ Nat.
Proof.
  intros ρ ρH.
  cbn. 
  eauto.
Qed.

Lemma ST_succ {v:Val n} :
  Γ ⊨v v ∈ Nat ->
  Γ ⊨v succ v ∈ Nat.
Proof.
(* FILL IN HERE *) Admitted.

Lemma ST_ifz v {e0:Tm n}{e1: Tm (S n)}{τ} ε1 ε2 ε : 
  Γ ⊨v v ∈ Nat -> 
  Γ ⊨ e0 ∈ τ @ ε1 -> 
  Nat .: Γ ⊨ e1 ∈ τ @ ε2 -> 
  ε1 <: ε -> 
  ε2 <: ε ->
  Γ ⊨ ifz v e0 e1 ∈ τ @ ε.
Proof.
(* FILL IN HERE *) Admitted.



(** Now let's repeat the argument for rec. *)
Lemma ST_rec  (v : Val (S n)) τ : 
  allows_rec_ty τ = true ->
  typing_val (τ .: Γ) v τ -> 
  Γ ⊨v (rec v) ∈ τ.
Proof.
  intros AR IH. intros ρ ρH.
  destruct τ; try done; destruct e; try done.
Qed.


Lemma ST_ret v τ ε : 
  Γ ⊨v v ∈ τ -> 
  (* ------------------------ *)
  Γ ⊨ (ret v) ∈ τ @ ε.
Proof.
(* FILL IN HERE *) Admitted.

Lemma ST_let e1 e2 τ1 τ2 ε1 ε2 ε: 
 Γ ⊨ e1 ∈ τ1 @ ε1 -> 
 (τ1 .: Γ) ⊨ e2 ∈ τ2 @ ε2 -> 
 ε1 ⊕ ε2 <: ε -> 
 Γ ⊨ let_ e1 e2 ∈ τ2 @ ε.
Proof.
(* FILL IN HERE *) Admitted.

Lemma ST_fold v τ : 
      Γ ⊨v v ∈ τ[(Mu τ)..] -> Γ ⊨v fold v ∈ Mu τ.
Proof.
  intros h.
  intros ρ hρ.
  cbn.
  eexists. eauto.
Qed.

Lemma ST_unfold v τ : 
  Γ ⊨v v ∈ Mu τ -> Γ ⊨ unfold v ∈ τ[(Mu τ)..] @ ⊤.
Proof.
  intros h ρ hρ.
  cbn. done.
Qed.

Lemma ST_inj b v τ1 τ2 : 
  Γ ⊨v v ∈ (if b then τ1 else τ2)  -> 
  Γ ⊨v inj b v ∈ Sum τ1 τ2.
Proof.
(* FILL IN HERE *) Admitted.


(* The autosubst notation interferes with this proof. *)
Lemma ST_case v e1 e2 τ τ1 τ2 ε : 
 Γ ⊨v v ∈ Sum τ1 τ2 -> 
 τ1 .: Γ ⊨ e1 ∈ τ @ ε -> 
 τ2 .: Γ ⊨ e2 ∈ τ @ ε -> 
 Γ ⊨ case v e1 e2 ∈ τ @ ε.
Proof.
  intros h1 h2 h3.
  intros ρ ρh.
  specialize (h1 ρ ρh).
  destruct h1 as [[v1 [EQ h1]]|[v2 [EQ h1]]].
  - cbn.
    unfold subst1, Subst_Val in EQ.
    destruct (subst_Val ρ v); cbn in EQ; try done.
    destruct b; cbn in EQ; try done. 
    inversion EQ. subst. clear EQ.
    destruct ε; try done.
    destruct (h2 (v1 .: ρ)) as [v' [EV hv']]. eapply semantic_subst_cons; eauto.
    exists v'. split; eauto.
    eapply ms_trans; eauto with rec.
    asimpl. eauto.
  - cbn.
    unfold subst1, Subst_Val in EQ.
    destruct (subst_Val ρ v); cbn in EQ; try done.
    destruct b; cbn in EQ; try done. 
    inversion EQ. subst. clear EQ.
    destruct ε; try done.
    destruct (h3 (v2 .: ρ)) as [v' [EV hv']]. eapply semantic_subst_cons; eauto.
    exists v'. split; eauto.
    eapply ms_trans; eauto with rec.
    asimpl. eauto.
Qed.



End Semtyping.

Fixpoint soundness_tm {n} (Γ : Ctx n) e τ ε :
  Γ |-e e ∈ τ @ ε -> Γ ⊨ e ∈ τ @ ε
with soundness_val {n} (Γ : Ctx n) v τ :
  Γ |-v v ∈ τ -> Γ ⊨v v ∈ τ.
Proof. 
  all: intros h ρ ρh; inversion h; subst.
  - eapply ST_ret; eauto.
  - eapply ST_let; eauto. eapply eff.refl.
  - eapply ST_app; eauto. 
(* FILL IN HERE *) Admitted.


