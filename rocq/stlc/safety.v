(* This file demonstrates a type safety proof based on progress and preservation. *)
Require Export stlc.syntax.
Require Export stlc.typing.
Require Export stlc.red.

Import TypingNotations.
Import RedNotations.

(* ----------------------------------------------------- *)

(** A renaming transforms terms from context Γ to context Δ
    when the types declared in Γ are consistent with the types
    in Δ. 
    The renaming operation generalizes "weakening" and "permutation"
    lemmas. The new context Δ can include new assumptions, and the 
    order doesn't have to match up. 
*)
Definition typing_renaming {n} (Δ : Ctx n) {m} (δ : fin m -> fin n)
  (Γ : Ctx m) : Prop := 
  forall x, Γ x = Δ (δ x).

(** The empty renaming is well-formed *)
Lemma typing_renaming_null {n} (Δ : Ctx n) :
  typing_renaming Δ null null.
Proof. unfold typing_renaming. intros x. destruct x. Qed.

Lemma typing_renaming_lift {n} (Δ : Ctx n) 
  {m} (Γ : Ctx m) (δ : fin m -> fin n) τ :
  typing_renaming Δ δ Γ ->
  typing_renaming (τ .: Δ) (var_zero .: δ >> ↑) (τ .: Γ).
Proof. 
  intro h.
  unfold typing_renaming in *.
  intros x.
  destruct x as [y|].
  cbn. rewrite h. done.
  cbn. done.
Qed.

Definition typing_subst {n} (Δ : Ctx n) {m} (σ : fin m -> Tm n)
  (Γ : Ctx m) : Prop := 
  forall x, typing Δ (σ x) (Γ x).

Lemma typing_subst_null {n} (Δ : Ctx n) :
  typing_subst Δ null null.
Proof. unfold typing_subst. intros x. destruct x. Qed.

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

(* Here's the first lemma about the typing judgement itself. 
   A well typed term can be renamed to a new context.
*)
Lemma renaming {n} (Γ : Ctx n) e τ {m} (Δ:Ctx m) δ : 
  typing Γ e τ -> typing_renaming Δ δ Γ -> typing Δ e⟨δ⟩ τ.
Proof.
  move=> h.
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

Qed.

Lemma typing_subst_lift {n} (Δ : Ctx n) {m} (σ : fin m -> Tm n)
  (Γ : Ctx m) τ : 
  typing_subst Δ σ Γ ->
  typing_subst (τ .: Δ) (var_Tm var_zero .: σ >> ren_Tm ↑) (τ .: Γ).
Proof.
  unfold typing_subst in *.
  intros h x.
  destruct x.
  + asimpl. replace ((σ >> ren_Tm ↑) f) with 
      ((ren_Tm ↑) (σ f)). 2: { asimpl. done. }
    eapply renaming. eapply h.
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

Qed.

Lemma preservation : forall e e', 
    Small.step e e' -> forall τ, typing null e τ -> typing null e' τ.
Proof.
  intros e e' hS.
  induction hS.
  all: intros τ hT.
  all: inversion hT; subst; clear hT.
  - (* s_beta *)
    inversion H2.
    eapply substitution. eauto.
    eapply typing_subst_cons; auto.
    eapply typing_subst_null; auto.
  - (* s_app_cong1 *)
    eapply t_app; eauto.
  - (* s_app_cong2 *)    
    eapply t_app; eauto.

Qed.

Lemma canonical_forms_Nat e : 
  typing null e Nat ->
  is_value e = true ->
  exists k, e = lit k.
Proof.
  intro h.
  dependent induction h.
  all: cbn.
  all: intro hV.
  all: try done.
  eauto.
Qed.

Lemma canonical_forms_Arr e τ1 τ2 : 
  typing null e (Arr τ1 τ2) ->
  is_value e = true ->
  exists e', e = abs e'.
Proof.
  intros h1 h2.
  destruct e; cbn in h2; try done.
  all: inversion h1.
  exists e. eauto.
Qed.

Lemma progress : forall e τ, 
    typing null e τ -> is_value e = true \/ exists e', Small.step e e'.
Proof.
  intros e τ hT.
  dependent induction hT.
  all: cbn.
  all: try solve [left; reflexivity].
  + destruct (IHhT1 e1); auto.
    ++ right. destruct (IHhT2 e2); auto.
       eapply canonical_forms_Arr in H; eauto.
       destruct H as [e1' ->].
       exists (e1' [e2 .: null]). eapply Small.s_beta; auto.
       destruct H0 as [e2' h2].
       exists (app e1 e2'). eapply Small.s_app_cong2; auto.
    ++ right.
       destruct H as [e1' h1].
       exists (app e1' e2).
       eapply Small.s_app_cong1; auto.

Qed.

(* Type safety states that a well-typed program does not get stuck. 
   in other words, it either runs forever or produces a value. 
*)

CoInductive safe_run (step : Tm 0 -> Tm 0 -> Prop) : Tm 0 -> Prop := 
  | safe_val v : is_value v = true -> safe_run step v
  | safe_step e e' : step e e' -> safe_run step e' -> safe_run step e.

Lemma type_safety : 
  forall e τ, typing null e τ -> safe_run Small.step e.
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
From Stdlib Require Import Psatz.

(* This relation captures the idea that an expression 
   takes exactly n steps.
   If n=0 then it takes no steps.
   If n=Sk, then it takes 1 step and then k steps.
 *)
Inductive step_n {A} (step : A -> A -> Prop) : nat -> A -> A -> Prop := 
  | s_done e : step_n step 0 e e
  | s_next k e1 e2 e3 : 
    step e1 e2 -> 
    step_n step k e2 e3 -> 
    step_n step (S k) e1 e3.

(* A program evaluates safely for k steps, if it either 
   halts with a value for some number of steps <= k, or 
   if it steps for k steps.
   A program is safe if k can be anything.
*)
Lemma type_safety_v2 k : forall (e : Tm 0) τ ,
    typing null e τ -> exists e', 
      (step_n Small.step k e e' /\ typing null e' τ) \/ 
      (exists j, j <= k /\ step_n Small.step j e e' /\ is_value e' = true).
Proof.
  induction k.
  + intros e τ h.
    exists e. left. split. eapply s_done; eauto. auto.
  + intros e τ h.
    destruct (progress _ _ h) as [v2|[e'' h2]].
    ++ exists e. right. exists 0. split; eauto. lia. split. 
       eapply s_done. auto.
    ++ (* e -> e'' *)
      move: (preservation _ _  h2 _ h) => h3.
      destruct (IHk _ _ h3) as [e' [[hS hT] | [j [LT [hS V]]]]].
      exists e'. left. split. eapply s_next; eauto. eauto.
      exists e'. right. exists (S j). repeat split; eauto. lia. eapply s_next; eauto.
Qed.

