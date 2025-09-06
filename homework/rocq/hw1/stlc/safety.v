(* This file demonstrates a type safety proof based on progress and preservation. *)
Require Export stlc.syntax.
Require Export stlc.typing.
Require Export stlc.red.

Import TypingNotations.
Import RedNotations.

(*** Renaming *)

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

(** Extend a renaming with a new definition *)
Lemma typing_renaming_cons {A}{n} (Δ : fin n -> A) 
  {m} (Γ : fin m -> A) (δ : fin m -> fin n) (τ : A) (x : fin n) :
  typing_renaming Δ δ Γ ->
  typing_renaming Δ (x .: δ) (Δ x .: Γ).
Proof. intro h. unfold typing_renaming in *. auto_case. Qed.

(** Lift a renaming to a new scope *)
Lemma typing_renaming_lift {A}{n} (Δ : fin n -> A) 
  {m} (Γ : fin m -> A) (δ : fin m -> fin n) (τ : A) :
  typing_renaming Δ δ Γ ->
  typing_renaming (τ .: Δ) (up_ren δ) (τ .: Γ).
Proof. intro h. unfold typing_renaming in *. auto_case. Qed.

(* Here's the first lemma about the typing judgement itself. 
   A well typed term can be renamed to a new context. *)

(** The typing judgement is stable under renaming *)
Lemma renaming {n} (Γ : Ctx n) e τ {m} (Δ:Ctx m) δ : 
  Γ |- e ∈ τ -> typing_renaming Δ δ Γ -> Δ |- e⟨δ⟩ ∈ τ.
Proof.
  intros h.
  (* ssreflect tactic for generalization. We need a strong IH. *)
  move: m Δ δ.
  induction h.
  all: intros m Δ δ tS.
  all: asimpl.
  - unfold typing_renaming in tS.
    rewrite tS.
    eapply t_var; eauto.
  - eapply t_abs; eauto.
    eapply IHh.
    eapply typing_renaming_lift; auto.
  - eapply t_app; eauto.
  - eapply t_lit; eauto.

(* FILL IN HERE *) Admitted.

(* Here's a more automated proof of the renaming lemma. *)
Example renaming' {n} (Γ : Ctx n) e τ {m} (Δ:Ctx m) δ : 
  Γ |- e ∈ τ -> typing_renaming Δ δ Γ -> Δ |- e⟨δ⟩ ∈ τ.
Proof.
  move=> h. move: m Δ δ. 
  (* every case except var *)
  induction h; intros; asimpl; 
    try econstructor; eauto using typing_renaming_lift.
  (* var case *)
  unfold typing_renaming in *; rewrite H; econstructor; eauto.
Qed.

(*** Substitution *)

(** A substitution transforms terms from context Γ to context Δ when the types
    declared in Γ are consistent with the types in Δ. *)
Definition typing_subst {n} (Δ : Ctx n) {m} (σ : fin m -> Tm n)
  (Γ : Ctx m) : Prop := 
  forall x, typing Δ (σ x) (Γ x).

(** The empty substitution closes the term *)
Lemma typing_subst_null {n} (Δ : Ctx n) :
  typing_subst Δ null null.
Proof. unfold typing_subst. auto_case. Qed.

(** The identity substitution preserves the context *)
Lemma typing_subst_id {n} (Δ : Ctx n) :
  typing_subst Δ var Δ.
Proof. unfold typing_subst. intro x. econstructor. Qed.

Lemma typing_subst_cons {n} (Δ : Ctx n) {m} (σ : fin m -> Tm n)
  (Γ : Ctx m) e τ : 
 typing Δ e τ ->
 typing_subst Δ σ Γ ->
 typing_subst Δ (e .: σ) (τ .: Γ).
Proof.
  intros tE tS.
  unfold typing_subst in *.
  intro x. destruct x as [y|].
  asimpl. eauto.
  asimpl. eauto.
Qed.

Lemma typing_subst_lift {n} (Δ : Ctx n) {m} (σ : fin m -> Tm n)
  (Γ : Ctx m) τ : 
  typing_subst Δ σ Γ ->
  typing_subst (τ .: Δ) (⇑ σ) (τ .: Γ).
Proof.
  unfold typing_subst in *.
  intros h.
  auto_case.
  + unfold_funcomp.
    eapply renaming; eauto. 
    unfold typing_renaming. asimpl. done.
  + asimpl. eapply t_var.
Qed.

Lemma substitution {n} (Γ : Ctx n) e τ {m} (Δ:Ctx m) σ : 
  typing Γ e τ -> typing_subst Δ σ Γ -> typing Δ e[σ] τ.
Proof.
  move=> h.
  move: m Δ σ.
  induction h.
  all: intros m Δ σ tS.
  all: asimpl.
  - eauto. 
  - eapply t_abs.
    eapply IHh.
    eapply typing_subst_lift. auto.
  - eapply t_app; eauto.
  - eapply t_lit; eauto.

(* FILL IN HERE *) Admitted.

(*** Preservation *)

Lemma preservation : forall e e', 
    e ⤳ e' -> forall τ, null |- e ∈ τ -> null |- e' ∈ τ.
Proof.
  intros e e' hS.
  induction hS.
  all: intros τ hT.
  all: inversion hT; subst; clear hT.
  - (* s_beta *)
    inversion H2.
    eapply substitution. eauto.
    eapply typing_subst_cons; auto.
    eapply typing_subst_id; auto.
  - (* s_app_cong1 *)
    eapply t_app; eauto.
  - (* s_app_cong2 *)    
    eapply t_app; eauto.

(* FILL IN HERE *) Admitted.


(*** Progress *)

(** Part of showing the progress lemma below is to define a lemma 
    about the closed values of for each type. These lemmas tell us 
    the form of that closed value. *)
Lemma canonical_forms_Nat e : 
  null |- e ∈ Nat ->
  is_value e = true ->
  exists k, e = lit k.
Proof.
  intros h V.
  (* focus on the cases where e is a value *)
  destruct e; cbn in h; try done.
  (* eliminate any values that don't have the right type *)
  all: inversion h.
  (* produce the sole witness *)
  eexists. eauto.
Qed.

Lemma canonical_forms_Arr e τ1 τ2 : 
  null |- e ∈ Arr τ1 τ2 ->
  is_value e = true ->
  exists e', e = abs e'.
Proof.
  intros h V.
  destruct e; cbn in h; try done.
  all: inversion h.
  eexists. eauto.
Qed.

Lemma progress : forall e τ, 
    null |- e ∈ τ -> is_value e = true \/ exists e', e ⤳ e'.
Proof.
  intros e τ hT.
  dependent induction hT.
  all: cbn.
  all: try solve [left; reflexivity].
  + destruct (IHhT1 e1); auto.
    ++ right. destruct (IHhT2 e2); auto.
       eapply canonical_forms_Arr in H; eauto.
       destruct H as [e1' ->].
       exists (e1' [e2..]). eapply Small.s_beta; auto.
       destruct H0 as [e2' h2].
       exists (app e1 e2'). eapply Small.s_app_cong2; auto.
    ++ right.
       destruct H as [e1' h1].
       exists (app e1' e2).
       eapply Small.s_app_cong1; auto.

(* FILL IN HERE *) Admitted.


(*** Type safety *)


(** No stuck terms *)

Definition not_stuck (e : Tm 0) := is_value e = true \/ exists e',  e ⤳ e'.

Theorem type_safety_not_stuck : 
  forall e τ, null |- e ∈ τ -> forall e', e ⤳* e' -> not_stuck e'.
Proof.
  intros.
  induction H0.
  eapply progress; eauto.
  eapply IHmulti.
  eapply preservation; eauto.
Qed.

(** Coinductive definition *)

(* Type safety states that a well-typed program does not get stuck. 
   in other words, it either runs forever or produces a value. 
*)

CoInductive safe_run (step : Tm 0 -> Tm 0 -> Prop) (e : Tm 0) : Prop := 
  | safe_val : is_value e = true -> safe_run step e
  | safe_step e' : step e e' -> safe_run step e' -> safe_run step e.

Lemma type_safety_coinductive : 
  forall e τ, null |- e ∈ τ -> safe_run Small.step e.
Proof.
  cofix h.
  intros e τ hT.
  destruct (progress e τ hT).
  + eapply safe_val. auto.
  + destruct H as [e' hE].
    eapply safe_step; eauto.
    eapply h.
    eapply preservation; eauto.
Qed.


(* Here is another way of stating type safety. *)

(* This relation captures the idea that an expression 
   takes exactly k steps.
   If n=0 then it takes no steps.
   If k=Sj, then it takes 1 step and then j steps.
 *)
Inductive step_k {A} (step : A -> A -> Prop) : nat -> A -> A -> Prop := 
  | s_done e : 
    step_k step 0 e e
  | s_next j e1 e2 e3 : 
    step e1 e2 -> 
    step_k step j e2 e3 -> 
    step_k step (S j) e1 e3.

(* A program evaluates safely for k steps, if it either 
   halts with a *value* for some number of steps <= k, or 
   if it steps for exactly k steps (i.e. doesn't get stuck). *)
Inductive safe_run_k (step : Tm 0 -> Tm 0 -> Prop) (k : nat) (e : Tm 0) :  Prop := 
  | safe_val_k j v : 
    step_k Small.step j e v -> is_value v = true -> j <= k -> safe_run_k step k e 
  | safe_step_k e' : 
    step_k Small.step k e e' -> safe_run_k step k e 
.

(* A program is *safe* if it runs safely for any number of steps. *)

Lemma type_safety_step_counting k : forall (e : Tm 0) τ ,
    null |- e ∈ τ -> safe_run_k Small.step k e.
Proof.
  induction k.
  + intros e τ h. eapply safe_step_k; eauto.
    eapply s_done; eauto.
  + intros e τ h.
    destruct (progress _ _ h) as [v2|[e'' h2]].
    ++ eapply safe_val_k with (j := 0); eauto.
       eapply s_done.
       eapply le_0_n.
    ++ destruct (IHk e'' τ).
       eapply preservation; eauto.
       - eapply safe_val_k with (j := S j); eauto.
         eapply s_next; eauto.
         eapply le_n_S; auto.
       - eapply safe_step_k; eauto.
         eapply s_next; eauto.
Qed.


