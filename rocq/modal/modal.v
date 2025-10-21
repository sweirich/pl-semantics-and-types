From Stdlib Require Export ssreflect.
From Stdlib Require Export Program.Equality.
Require Export common.core.
Require Export common.fintype.

Require Export common.fin_util.
Require Export common.relations.
Require Export common.renaming.

Require Export modal.syntax.

(** Define a notation scope specific to this language. *)
Declare Scope modal_scope.

Module SyntaxNotations.
Export ScopedNotations.
Notation "⇑" := (up_Val_Val) : modal_scope.
Notation "⇑ σ" := (var var_zero .: σ >> ren_Val ↑) 
                    (only printing, at level 0) : modal_scope.
End SyntaxNotations.

Export SyntaxNotations.

Open Scope subst_scope.
Open Scope modal_scope.
Create HintDb modal.

(** Small step, substitution-based reduction *)

Inductive step : Tm 0 -> Tm 0 -> Prop := 
 | s_beta e v : 
    step (app (abs e) v) (e [v..])

 | s_letv e v : 
    step (let_ (ret v) e) (e [v..])       

 | s_let_cong e1 e1' e2 : 
    step e1 e1' ->
    step (let_ e1 e2) (let_ e1' e2)

 | s_app_fun (v1 : Tm 2) (v2 : Val 0) : 
    step (app (fun_ v1) v2) (v1[v2 .: (fun_ v1)..])

 | s_bind v e :
    step (unbox (ret (box v)) e) (e [v..])

 | s_bind_cong e1 e1' e2 :
    step e1 e1' ->
    step (unbox e1 e2) (unbox e1' e2)
.


#[export] Hint Constructors step : modal.

Definition not_box (τ : Ty) := 
  match τ with 
  | Box _ => False
  | _ => True
  end.

Definition Ctx (n : nat) := fin n -> Ty.

Inductive typing_val {n} (Γ : Ctx n) : Val n -> Ty  -> Prop := 
  | t_var x : 
    typing_val Γ (var x) (Γ x)

  | t_lit k : 
    typing_val Γ (lit k) Nat

  | t_abs e τ1 τ2 : 
    typing (τ1 .: Γ) e τ2 ->
    typing_val Γ (abs e) (Arr τ1 τ2)

  | t_fun e τ τ1 τ2  : 
    τ = Arr τ1 (Box τ2) ->
    typing (τ1 .: (τ .: Γ)) e (Box τ2)  -> 
    typing_val Γ (fun_ e) τ

  | t_pure v τ : 
    typing_val Γ v τ -> 
    typing_val Γ (box v) (Box τ)

with typing {n} (Γ : Ctx n) : Tm n -> Ty  -> Prop := 
  | t_ret v τ :
    typing_val Γ v τ ->
    typing Γ (ret v) τ 

  | t_let e1 e2 τ1 τ2 : 
    typing Γ e1 τ1 ->
    not_box τ1 ->
    typing (τ1 .: Γ) e2 τ2 ->
    typing Γ (let_ e1 e2) τ2

  | t_bind e1 e2 τ1 τ2  :
    typing Γ e1 (Box τ1)  ->
    typing (τ1 .: Γ) e2 (Box τ2) ->
    typing Γ (unbox e1 e2) (Box τ2)

  | t_app v1 v2 τ1 τ2  : 
    typing_val Γ v1 (Arr τ1 τ2) -> 
    typing_val Γ v2 τ1 -> 
    typing Γ (app v1 v2) τ2 
.

Definition t_var' {n} (Γ : Ctx n) x τ :
  Γ x = τ -> typing_val Γ (var x) τ.
intros <-. eapply t_var. Qed.

#[export] Hint Resolve t_var' : modal.

#[export] Hint Constructors typing_val typing : modal.

Module Notations.
Export SyntaxNotations.
Notation "e ~> e'" := (step e e') (at level 70) : modal_scope.
Notation "e ~>* e'" := (multi step e e') (at level 70) : modal_scope.
Notation "Γ |-v v ∈ τ" := (typing_val Γ v τ) (at level 70) : rec_scope.
Notation "Γ |-e e ∈ τ" := (typing Γ e τ) (at level 70) : rec_scope.
End Notations.

Import Notations.


(** multistep congruence for let *)
Lemma ms_unbox_cong e1 e1' e2 : 
  e1 ~>* e1' -> unbox e1 e2 ~>* unbox e1' e2.
Proof.
  induction 1. eapply ms_refl.
  eapply ms_trans; eauto.
  econstructor; eauto.
Qed.

Lemma ms_let_cong e1 e1' e2 : 
  e1 ~>* e1' -> let_ e1 e2 ~>* let_ e1' e2.
Proof.
  induction 1. eapply ms_refl.
  eapply ms_trans; eauto.
  econstructor; eauto.
Qed.

Ltac impossible_var := 
  match goal with | [ x : (fin 0) |- _ ] => destruct x end.

Open Scope rec_scope.
Import Notations.


(** * Renaming lemma *)

Fixpoint renaming_val {n} (Γ : Ctx n) v τ {m} (Δ:Ctx m) δ : 
  Γ |-v v ∈ τ -> typing_renaming Δ δ Γ -> Δ |-v v⟨δ⟩ ∈ τ
with renaming_tm {n} (Γ : Ctx n) e τ {m} (Δ:Ctx m) δ  : 
  Γ |-e e ∈ τ  -> typing_renaming Δ δ Γ -> Δ |-e e⟨δ⟩ ∈ τ .
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

Hint Resolve renaming_val renaming_tm : modal.

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
  intros h. auto_case; eauto with renaming modal. 
Qed.


Lemma typing_subst_lift2 {n} (Δ : Ctx n) {m} (σ : fin m -> Val n)
  (Γ : Ctx m) τ1 τ2  : 
  typing_subst Δ σ Γ -> typing_subst (τ1 .: (τ2 .: Δ)) (⇑(⇑ σ)) (τ1 .: (τ2 .: Γ)).
Proof.
  unfold typing_subst in *.
  intros h. auto_case; eauto with renaming modal. 
Qed.

(** Add the substitution lemmas as hints *)
#[export] Hint Resolve typing_subst_lift typing_subst_cons
             typing_subst_id typing_subst_null : modal.

Fixpoint substitution_val {n} (Γ : Ctx n) v τ {m} (Δ:Ctx m) σ : 
  Γ |-v v ∈ τ -> typing_subst Δ σ Γ -> Δ |-v v[σ] ∈ τ
with
  substitution_tm {n} (Γ : Ctx n) e τ {m} (Δ:Ctx m) σ : 
  Γ |-e e ∈ τ -> typing_subst Δ σ Γ -> Δ |-e e[σ] ∈ τ.
Proof.
  all: intros h tS.
  all: inversion h; subst.
  all: cbn; asimpl.
  all: try solve [econstructor; eauto with modal].
  - unfold typing_subst in tS. eauto.
  - eapply t_fun; eauto.
    eapply substitution_tm with (σ := ⇑ (⇑ σ)) in H0. 2: eauto with modal.
    asimpl in H0. eauto.
Qed.

#[export] Hint Resolve substitution_val substitution_tm : modal.

(** * Type safety *)

Lemma preservation e e' τ :
  null |-e e ∈ τ  -> e ~> e' -> null |-e e' ∈ τ .
Proof. 
  intro h.
  move: e'.
  dependent induction h.
  all: intros e' S; inversion S; subst.
(* FILL IN HERE *) Admitted.

Lemma progress e τ :
  null |-e e ∈ τ -> (exists v, e = ret v) \/ (exists e', e ~> e').
Proof.
  intros h.
  dependent induction h.
(* FILL IN HERE *) Admitted.

(** Translation to effect system. *)

Require div.div.
Import FinValues.

(** * Aux definitions for the DIV language *)

Module DIV.
Include div.typesyntax.Core.
Include rec.syntax.Core.
Include div.div.
Arguments Nat{_}.
Arguments Arr{_}.
Arguments zero{_}.
Arguments succ{_}.
Arguments let_{_}.
Arguments app{_}.
Arguments var{_}.
Arguments ret{_}.
Arguments abs{_}.
Arguments rec{_}.


Definition app_tm {n} (v : DIV.Val n) (e : DIV.Tm n) :=
  let_ e (app (v ⟨↑⟩) (var f0)).

Lemma t_app_tm n (Γ:Ctx n) v e τ1 τ2 ε1 ε2:
  typing_val Γ v (Arr τ1 ε1 τ2) -> typing Γ e τ1 ε2 -> 
  typing Γ (app_tm v e) τ2 (join ε2 ε1).
Proof. 
  intros h1 h2.
  unfold app_tm. eauto with rec renaming.
Qed.

Definition app_tm_val {n} (e1 : DIV.Tm n) (v : DIV.Val n) :=
  DIV.let_ e1 (DIV.app (DIV.var f0) v⟨↑⟩).
Lemma t_app_tm_val n (Γ:Ctx n) e1 v τ1 τ2 ε1 ε3 :
  typing Γ e1 (Arr τ1 ε3 τ2) ε1 -> typing_val Γ v τ1 -> 
  typing Γ (app_tm_val e1 v) τ2 (join ε1 ε3).
Proof. 
  intros h1 h2.
  unfold app_tm_val.
  eapply t_let; eauto with rec renaming.
  eapply t_app; eauto with rec.
  eapply t_var'; eauto with rec renaming. done.
  eapply renaming_val; eauto with renaming.
Qed.

Fixpoint to_nat_val {n} (x : nat) : Val n := 
  match x with 
  | 0 => zero
  | S m => succ (to_nat_val m)
  end.


Lemma typing_to_nat_val {n} (Γ : Ctx n) (k : nat) : 
  typing_val Γ (to_nat_val k) Nat.
Proof. 
  induction k; cbn; eauto with rec.
Qed.

Definition eta {n} (v : Val n) : Val n := 
  abs (ret (abs (app_tm_val (app v⟨↑⟩⟨↑⟩ (var f1)) (var f0)))).
 
Lemma t_eta {n} Γ (v : Val n) τ1 τ2 τ3 ε1 ε2 : 
  typing_val Γ v (Arr τ1 ε1 (Arr τ2 ε2 τ3)) -> 
  typing_val Γ (eta v) (Arr τ1 Bot (Arr τ2 (join ε1 ε2) τ3)).
Proof.
(* FILL IN HERE *) Admitted.

End DIV.

Module MOD_DIV.


(** * The translation *)

Fixpoint trans_ty (t : Ty) : DIV.Ty 0 := 
  match t with 
  | Nat => DIV.Nat  
  | Arr t1 t2 => DIV.Arr (trans_ty t1) eff.Bot (trans_ty t2)
  | Box t => DIV.Arr DIV.Nat eff.Top (trans_ty t)
  end
.


Fixpoint trans_tm {n} (e : Tm n) {struct e} : rec.syntax.Core.Tm n := 
  match e with 
  | ret v => DIV.ret (trans_val v)
  | app v1 v2 => DIV.app (trans_val v1) (trans_val v2)
  | let_ e1 e2 => 
      DIV.let_ (trans_tm e1) (trans_tm e2)
  | unbox t1 t2 => 
      DIV.ret (DIV.abs
                 (DIV.let_ 
                    (DIV.app_tm_val (trans_tm t1)⟨↑⟩ DIV.zero)
                    (DIV.app_tm_val (trans_tm t2)⟨up_ren shift⟩ DIV.zero)))
  end
with trans_val {n} (v : Val n) {struct v} : rec.syntax.Core.Val n := 
       match v with 
       | var f => DIV.var f
       | abs t => DIV.abs (trans_tm t)
       | lit k => DIV.to_nat_val k
       | box v => DIV.abs (DIV.ret (trans_val v) ⟨↑⟩)
       | fun_ e => DIV.eta (DIV.rec ((DIV.abs (trans_tm e))[(DIV.eta (DIV.var f0)) .: shift >> DIV.var]))
       end.

(* Because we are representing contexts via functions, sometimes we need an 
   axiom to reason about them. *)
From Stdlib Require Import FunctionalExtensionality.

Lemma scons_comp {n}{A} (Γ : Ctx n) τ (h : Ty -> A) : 
  ((τ .: Γ) >> h) = (h τ) .: (Γ >> h).
asimpl. unfold funcomp, scons.
eapply functional_extensionality.
intro x. destruct x; eauto.
Qed.


Lemma type_pres n (Γ : Ctx n) e τ : 
  typing Γ e τ -> 
      DIV.typing (Γ >> trans_ty) (trans_tm e) (trans_ty τ) eff.Bot
with type_pres_val n (Γ : Ctx n) v τ :
  typing_val Γ v τ ->
       DIV.typing_val (Γ >> trans_ty) (trans_val v) (trans_ty τ).
Proof.
(* FILL IN HERE *) Admitted.

Notation "| e |"    := (trans_tm e) (only printing).
Notation "| e |"    := (trans_val e) (only printing).

Notation "e ~> e'"  := (reduction.Small.step e e') (at level 70, only printing).
Notation "e ~>* e'" := (multi reduction.Small.step e e') (at level 70, only printing).


End MOD_DIV.    
    
