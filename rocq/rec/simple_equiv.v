(** Type-indexed equivalence relations for a stack-based, 
    fine-grained CBV, simply-typed lambda calculus
 *)

Require Export rec.typesyntax.
Disable Notation "↑__Ty" (all).
Disable Notation "'__Ty'" (all).

(** Use stack-based operational semantics *)

Require Export rec.stack.
From Stdlib Require Import FunctionalExtensionality.
From Stdlib Require Import PropExtensionality.
From Stdlib Require Import Relations RelationClasses.

Import SyntaxNotations.
Import Lists.List.ListNotations.

Open Scope list_scope.
Open Scope rec_scope.

(** * STLC typing rules *)

Definition Ctx (n : nat) := fin n -> Ty 0.

Inductive typing_val {n} (Γ : Ctx n) : Val n -> Ty 0 -> Prop := 
  | t_var x : 
    typing_val Γ (var x) (Γ x)

  | t_zero : 
    typing_val Γ zero Nat

  | t_succ k :
    typing_val Γ k Nat -> 
    typing_val Γ (succ k) Nat

 | t_abs e τ1 τ2 : 
    typing (τ1 .: Γ) e τ2 -> 
    typing_val Γ (abs e) (Arr τ1 τ2)

 | t_unit :
    typing_val Γ unit Unit

with typing {n} (Γ : Ctx n) : Tm n -> Ty 0 -> Prop := 
  | t_ret v τ :
    typing_val Γ v τ ->
    typing Γ (ret v) τ

  | t_let e1 e2 τ1 τ2 :
    typing Γ e1 τ1 ->
    typing (τ1 .: Γ) e2 τ2 ->
    typing Γ (let_ e1 e2) τ2

  | t_app v1 v2 τ1 τ2 : 
    typing_val Γ v1 (Arr τ1 τ2) -> 
    typing_val Γ v2 τ1 -> 
    typing Γ (app v1 v2) τ2

  | t_ifz v e0 e1 τ :
    typing_val Γ v Nat -> 
    typing Γ e0 τ -> 
    typing (Nat .: Γ) e1 τ -> 
    typing Γ (ifz v e0 e1) τ
.

Definition t_var' {n} (Γ : Ctx n) x τ   : Γ x = τ -> typing_val Γ (var x) τ.
intros <-. eapply t_var. Qed.

#[export] Hint Resolve t_var' : rec.

#[export] Hint Constructors typing_val typing : rec.

Inductive typing_frame : frame -> Ty 0 -> Ty 0 -> Prop := 

  | ft_let e1 τ1 τ2 : 
    typing (τ1 .: null) e1 τ2  ->
    typing_frame (f_let e1) τ1 τ2.

Inductive typing_stack : stack -> Ty 0 -> Ty 0 -> Prop := 
  | st_nil τ : 
    typing_stack nil τ τ

  | st_cons f s τ τ' τ'' : 
    typing_frame f τ τ' ->
    typing_stack s τ' τ''  ->
    typing_stack (cons f s) τ τ''
.

Inductive machine_ok : machine -> Ty 0 -> Prop := 
  | m_eval s e τ τ'  : 
    typing_stack s τ τ' -> 
    typing null e τ ->
    machine_ok (s, e) τ'.


#[export] Hint Constructors typing_stack typing_frame machine_ok : rec.

Module Notations.
Export stack.Notations.
Notation "Γ |-v v ∈ τ" := (typing_val Γ v τ) (at level 70) : rec_scope.
Notation "Γ |-e e ∈ τ" := (typing Γ e τ) (at level 70) : rec_scope.
Notation "|-f f ∈ τ1 ~> τ2" := (typing_frame f τ1 τ2) (at level 70): rec_scope.
Notation "|-s s ∈ τ1 ~> τ2" := (typing_stack s τ1 τ2) (at level 70) : rec_scope.
End Notations.

Import Notations.

(** * Basic properties of the typing relation *)

(** Renaming and substitution for stacks. Note: autosubst doesn't generate
    these instances for us. *)

(** Renaming lemma *)

Fixpoint renaming_val {n} (Γ : Ctx n) v τ {m} (Δ:Ctx m) δ : 
  Γ |-v v ∈ τ -> typing_renaming Δ δ Γ -> Δ |-v v⟨δ⟩ ∈ τ
with renaming_tm {n} (Γ : Ctx n) e τ {m} (Δ:Ctx m) δ : 
  Γ |-e e ∈ τ -> typing_renaming Δ δ Γ -> Δ |-e e⟨δ⟩ ∈ τ.
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


(** A tactic to invert typing hypotheses in the context, when the 
    syntax of the value/term/stack/frame is not a variable. *)
Ltac invert_typing := 
  match goal with 
    | [ H : typing_val _ (_ _) _ |- _ ] => inversion H; subst; clear H
    | [ H : typing_stack (cons _ _) _ _ |- _ ] => inversion H; subst; clear H
    | [ H : typing _ (_ _) _ |- _ ] => inversion H; subst; clear H
    | [ H : typing_frame (_ _) _ _ |- _ ] => inversion H; subst; clear H
    end.


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
Qed. 

(** Add the substitution lemmas as hints *)
#[export] Hint Resolve typing_subst_lift typing_subst_cons
             typing_subst_id typing_subst_null : rec.

Fixpoint substitution_val {n} (Γ : Ctx n) v τ {m} (Δ:Ctx m) σ : 
  Γ |-v v ∈ τ -> typing_subst Δ σ Γ -> Δ |-v v[σ] ∈ τ
with
  substitution_tm {n} (Γ : Ctx n) e τ {m} (Δ:Ctx m) σ : 
  Γ |-e e ∈ τ -> typing_subst Δ σ Γ -> Δ |-e e[σ] ∈ τ.
Proof.
  all: intros h tS.
  all: inversion h; subst.
  all: cbn.
  all: try solve [econstructor; eauto with rec].
  - unfold typing_subst in tS. eauto.
Qed.

#[export] Hint Resolve substitution_val substitution_tm : rec.


(** * Preservation lemma *)

Lemma primitive_preservation e e' τ:
  (null |-e e ∈ τ) -> e ~>> e' -> null |-e e' ∈ τ.
Proof.
  intro h.
  dependent induction h.
  all: intros hS; inversion hS; subst.
  all: eauto with rec.
  all: try solve [inversion H; eauto with rec].
Qed.

Lemma machine_preservation m m' τ: machine_ok m τ -> m ↦ m' -> machine_ok m' τ.
Proof.
  intros h hS.
  (* invert machine_ok and step *)
  inversion h; subst;
  inversion hS; subst; clear hS.
  (* invert typing judgement in each case *)
  all: repeat invert_typing.
  - (* s_prim *) 
    econstructor; eauto. eapply primitive_preservation; eauto.
  - (* s_pop *)
    econstructor; eauto with rec.
  - (* s_push *)
    econstructor; eauto with rec.
Qed.

(** * Program contexts *)



(** * Nat-based equivalence and approximation *)

(* Because we are working with a terminating language, we don't need
   to use step counts in our definitions. 
   Furthermore, as we don't need to work with approximations, our 
   base relation can be equivalence.

   Note that this definition does *not* require the two machines 
   to terminate.
*)

Definition nat_approx : relation machine := 
  fun m1 m2 => 
  forall v, is_nat v = true -> 
       m1 ↦* (nil,ret v) -> m2 ↦* (nil, ret v).

Definition nat_equiv : relation machine := 
  fun m1 m2 => nat_approx m1 m2 /\ nat_approx m2 m1.

Infix "⊑ℕ" := nat_approx (at level 70).
Infix "≡ℕ" := nat_equiv  (at level 70).

(* Nat approximation is a preorder *)

Instance nat_approx_reflexive : Reflexive nat_approx.
Proof. intros m. unfold nat_approx. intros v h. tauto. Qed.

Instance nat_approx_transitive : Transitive nat_approx. 
Proof. intros m n p.
       unfold nat_approx. 
       intros h1 h2 v hV.
       specialize(h1 v hV).
       specialize(h2 v hV).
       intros h.
       eapply ms_app; eauto.
       eapply ms_refl.
Qed.

(* Nat equivalence is an equivalence relation *)

Instance nat_equiv_reflexive : Reflexive nat_equiv.
intros m. split; reflexivity. Qed.
Instance nat_equiv_transitive : Transitive nat_equiv.
intros m n p [h1 h1'] [h2 h2']. split; eauto using nat_approx_transitive. Qed.
Instance nat_equiv_symmetric : Symmetric nat_equiv.
intros m n [h h']. split; eauto. Qed.

(* Nat equivalence includes the step relation *)

Lemma nat_step m1 m2: m1 ↦ m2 -> m1 ≡ℕ m2.
Proof. 
  intro h. split.
  - intros v IsNat EV1.
    inversion EV1; subst. inversion h. inversion H2.
    eapply StackSmall.deterministic in h; eauto. subst.
    eauto.
  - intros v IsNat EV1.
    eapply ms_trans; eauto.
Qed.

Lemma nat_multi m1 m2: m1 ↦* m2 -> m1 ≡ℕ m2.
Proof. 
  intros h. induction h.
  reflexivity.
  transitivity e2; eauto using nat_step.
Qed.

(** * Typed relations on open terms *)

(* generalize so we can talk about both Tms and Vals *)

Definition typing_judgement T := 
  forall n (Γ : Ctx n), T n -> Ty 0 -> Prop.

Definition typed_relation T := 
  forall n (Γ : Ctx n), T n -> T n -> Ty 0 -> Prop.

Class TypedRelation T (Ty : typing_judgement T) (R : typed_relation T) := 
  { typed1 : forall {n} {Γ : Ctx n} {e e' τ}, R _ Γ e e' τ -> Ty _ Γ e τ ;
    typed2 : forall {n} {Γ : Ctx n} {e e' τ}, R _ Γ e e' τ -> Ty _ Γ e' τ 
  }. 


(* Must equate all well-typed terms to themselves *)

Definition TypedReflexive {T : nat -> Type}
  (ty : typing_judgement T) (R : typed_relation T) 
  : Prop := 
  forall n Γ e τ, ty n Γ e τ -> R n Γ e e τ.
Existing Class TypedReflexive.

Definition TypedTransitive {T : nat -> Type}
  (R : typed_relation T) 
  : Prop := 
forall n Γ (t1 t2 t3 : T n) τ, 
      R _ Γ t1 t2 τ -> R _ Γ t2 t3 τ -> R _ Γ t1 t3 τ.
Existing Class TypedTransitive.

Definition Adequate (RE : typed_relation Tm) := 
  forall e e', RE _ null e e' Nat -> nat_equiv (nil, e) (nil, e').
Existing Class Adequate.

Class Compatible (RE : typed_relation Tm)
                 (RV : typed_relation Val) := 
  { val_var (n : nat) (Γ : Ctx n) x :
      RV n Γ (var x) (var x) (Γ x) ;

    val_unit (n : nat) (Γ : Ctx n): 
      RV n Γ unit unit Unit ;

    val_zero (n : nat) (Γ : Ctx n): 
      RV n Γ zero zero Nat ;

    val_succ (n : nat) (Γ : Ctx n) x y :
      RV n Γ x y Nat ->
      RV n Γ (succ x) (succ y) Nat ;

    val_abs (n : nat) (Γ : Ctx n) e1 e2 τ1 τ2 : 
      RE _ (τ1 .: Γ) e1 e2 τ2 -> 
      RV n Γ (abs e1) (abs e2) (Arr τ1 τ2) ;

    comp_ret (n : nat) (Γ : Ctx n) v1 v2 τ: 
      RV _ Γ v1 v2 τ ->
      RE n Γ (ret v1) (ret v2) τ;

    comp_let (n : nat) (Γ : Ctx n) e1 e2 e1' e2' τ1 τ: 
      RE _ Γ e1 e2 τ1 -> 
      RE _ (τ1 .: Γ) e1' e2' τ ->
      RE n Γ (let_ e1 e1') (let_ e2 e2') τ ;

    comp_ifz n (Γ : Ctx n) v1 v2 e1 e2 e1' e2' τ : 
      RV _ Γ v1 v2 Nat -> 
      RE _ Γ e1 e2 τ -> 
      RE _ (Nat .: Γ) e1' e2' τ -> 
      RE n Γ (ifz v1 e1 e1') (ifz v2 e2 e2') τ ;

    comp_app (n : nat) (Γ : Ctx n) v1 v2 v1' v2' τ1 τ2 :
      RV _ Γ v1 v2 (Arr τ1 τ2) -> 
      RV _ Γ v1' v2' τ1 -> 
      RE n Γ (app v1 v1') (app v2 v2') τ2  ;
}.

Inductive CTX n (Γ:Ctx n) (e e' : Tm n) τ : Prop := 
  rel : forall RE RV, 
      Compatible RE RV -> 
      Adequate RE -> 
      TypedTransitive RE ->
      TypedRelation Tm (@typing) RE ->
      TypedRelation Val (@typing_val) RV ->
      RE n Γ e e' τ -> CTX n Γ e e' τ.


(** Adequacy of CTX is straightforward *)

Instance Adequate_CTX : Adequate CTX.
Proof.
  unfold Adequate.
  intros e e' h.
  inversion h.
  eapply H0; eauto.
Qed.


Fixpoint Compatible_refl_RE {RE RV}
  `{ Compatible RE RV } : forall n Γ e τ, Γ |-e e ∈ τ -> RE n Γ e e τ
with Compatible_refl_RV {RE RV}
  `{ Compatible RE RV } : forall n Γ v τ, Γ |-v v ∈ τ -> RV n Γ v v τ.
all: intros n Γ ? τ h.
all: inversion h; subst.
- eapply comp_ret; eauto. eapply Compatible_refl_RV; eauto.
- eapply comp_let; eauto. eapply Compatible_refl_RE; eauto.
  eapply Compatible_refl_RE; eauto.
- eapply comp_app; eapply Compatible_refl_RV; eauto.
- eapply comp_ifz. 
  eapply Compatible_refl_RV; eauto. 
  eapply Compatible_refl_RE; eauto.
  eapply Compatible_refl_RE; eauto.
- eapply val_var; eauto.
- eapply val_zero; eauto.
- eapply val_succ; eauto.
  eapply Compatible_refl_RV; eauto.
- eapply val_abs; eauto. 
  eapply Compatible_refl_RE; eauto.
- eapply val_unit; eauto.
Qed.


(* ------------------------------------------------------------------ *)

(** Transtivity of CTX *)

Inductive OR_star {T : nat -> Type} 
  (RE1 RE2: typed_relation T) n (Γ : Ctx n) (t1 t2 : T n) τ : Prop := 
  | OR_1 : RE1 n Γ t1 t2 τ -> OR_star RE1 RE2 n Γ t1 t2 τ
  | OR_2 : RE2 n Γ t1 t2 τ -> OR_star RE1 RE2 n Γ t1 t2 τ
  | OR_trans t3 : OR_star RE1 RE2 n Γ t1 t3 τ
    -> OR_star RE1 RE2 n Γ t3 t2 τ
    -> OR_star RE1 RE2 n Γ t1 t2 τ. 

Instance Reflexive_OR_star {T}{Ty} {RE1 RE2 : typed_relation T} 
  `{TypedReflexive T Ty RE1} : TypedReflexive Ty (OR_star RE1 RE2).
Proof.
unfold TypedReflexive.
- intros n Γ e τ h. eapply OR_1. eapply H; eauto.
Qed.

Instance Transitive_OR_star {T} {RE1 RE2 : typed_relation T} :
  TypedTransitive (OR_star RE1 RE2).
Proof.
- intros n t1 t2 t3 O1 O2.    
  eapply OR_trans; eauto.
Qed.

Instance Adequate_OR_star {RE1 RE2 : typed_relation Tm} `{Adequate RE1} `{Adequate RE2} : Adequate (OR_star RE1 RE2). 
Proof.
unfold Adequate in *.
intros e e' O. induction O; eauto.
transitivity ((nil : stack), t3); eauto.
Qed.

Instance Typed_OR_star {T}{Ty}{RE1 RE2 : typed_relation T} 
  `{TypedRelation T Ty RE1} `{TypedRelation T Ty RE2} : 
  TypedRelation T Ty (OR_star RE1 RE2). 
Proof.
  split.
  - intros.
    destruct H as [ty1 ty2].
    destruct H0 as [ty1' ty2'].
    dependent induction H1; eauto.
  - intros.
    destruct H as [ty1 ty2].
    destruct H0 as [ty1' ty2'].
    dependent induction H1; eauto.
Qed.

Ltac compat_case H1 f := 
dependent induction H1; [ 
  eapply OR_1; eapply f; eauto |
  eapply OR_2; eapply f; eauto |
  eapply OR_trans; eauto].


Instance Compatible_OR_star 
  {RE1 RE2 : typed_relation Tm}
  {RV1 RV2 : typed_relation Val} 
   `{TypedReflexive Tm (@typing) RE1} `{TypedReflexive Tm (@typing) RE2}
   `{TypedTransitive Tm RE1} `{TypedTransitive Tm RE2}
   `{TypedReflexive _ (@typing_val) RV1} `{TypedReflexive _ (@typing_val) RV2}
   `{TypedRelation Tm (@typing) (OR_star RE1 RE2)} 
   `{TypedRelation _ (@typing_val) (OR_star RV1 RV2)} 
   `{Compatible RE1 RV1} `{Compatible RE2 RV2} : 
  Compatible (OR_star RE1 RE2) (OR_star RV1 RV2).      
Proof.               
constructor.
all: intros.
- eapply OR_1; eapply val_var; eauto.
- eapply OR_1; eapply val_unit; eauto.
- eapply OR_1; eapply val_zero; eauto.
- compat_case H9 @val_succ.
- compat_case H9 @val_abs.
- compat_case H9 @comp_ret.
- destruct H5 as [h1 h2].
  eapply OR_trans with (t3 := let_ e2 e1').  
  + compat_case H9 @comp_let; eapply s_refl; eauto.
  + compat_case H10 @comp_let; eapply s_refl; eauto.
- destruct H5 as [h1 h2].
  destruct H6 as [h3 h4].
  eapply OR_trans with (t3 := ifz v2 e1 e1').
  + compat_case H9 @comp_ifz; eapply s_refl; eauto.
  + eapply OR_trans with (t3 := ifz v2 e2 e1').
    * compat_case H10 @comp_ifz; eapply s_refl; eauto.
    * compat_case H11 @comp_ifz; eapply s_refl; eauto.
- destruct H5 as [h1 h2].
  destruct H6 as [h3 h4].
  eapply OR_trans with (t3 := app v2 v1').
  + compat_case H9 @comp_app; eapply s_refl; eauto.
  + compat_case H10 @comp_app; eapply s_refl; eauto.
Qed. 

Instance Transitive_CTX : TypedTransitive CTX.
intros n Γ t1 t2 t3 τ C1 C2.
  destruct C1 as [RE1 RV1 ? ? ? ? R1].
  destruct C2 as [RE2 RV2 ? ? ? ? R2].
  eapply (rel n Γ t1 t3 τ (OR_star RE1 RE2) (OR_star RV1 RV2)).
  + eapply Compatible_OR_star; eauto.
    Unshelve. 
    unfold TypedReflexive.
    eapply Compatible_refl_RE.
    unfold TypedReflexive.
    eapply Compatible_refl_RE.
    unfold TypedReflexive.
    eapply Compatible_refl_RV.
    unfold TypedReflexive.
    eapply Compatible_refl_RV.
  + eapply Adequate_OR_star; eauto.
  + eapply Transitive_OR_star; eauto.
  + eapply Typed_OR_star; eauto.
  + eapply Typed_OR_star; eauto.
  + eapply OR_trans. eapply OR_1; eauto.
    eapply OR_2; eauto.
Qed.

Instance TypedRelation_CTX : TypedRelation Tm (@typing) CTX.
split.
- intros. inversion H. eapply typed1; eauto.
- intros. inversion H. eapply typed2; eauto.
Qed.


(** ------------------------------------------------- *)

(*
Variant ContextType : Type := TmCtx | ValCtx.
Definition CT (T : ContextType) : nat -> Type := 
  match T with | TmCtx => Tm | ValCtx => Val end.

(* A context has two natural number indices. The first is the scope of the
  hole, the second is the scope of the plugged term or value. (See definition
  of plug below.)

  A context also has two 'ContextType' indices. The first is the type of the
  hole. Do we plug terms or values in to this Context. The second describes
  whether this Context produces a term or value. For the second, we could
  split the Context type in to TmContext and ValContext. However, when we talk
  about composing contexts it is useful to be able to abstract over this
  index.  
*)
Inductive Context (m : nat) : nat -> ContextType -> ContextType -> Type :=
  | c_hole {T}    : Context m m T T
  | c_app1 {n T}  : Context m n T ValCtx -> Val n -> Context m n T TmCtx
  | c_app2 {n T}  : Val n -> Context m n T ValCtx -> Context m n T TmCtx
  | c_let1 {n T}  : Context m n T TmCtx -> Tm (S n) -> Context m n T TmCtx
  | c_let2 {n T}  : Tm n -> Context m (S n) T TmCtx -> Context m n T TmCtx
  | c_ifz1 {n T}  : Context m n T ValCtx -> Tm n -> Tm (S n) -> Context m n T TmCtx
  | c_ifz2 {n T}  : Val n -> Context m n T TmCtx -> Tm (S n) -> Context m n T TmCtx
  | c_ifz3 {n T}  : Val n -> Tm n -> Context m (S n) T TmCtx -> Context m n T TmCtx
  | c_ret  {n T}  : Context m n T ValCtx -> Context m n T TmCtx
  | v_abs {n T}   : Context m (S n) T TmCtx -> Context m n T ValCtx
  | v_succ {n T}  : Context m n T ValCtx -> Context m n T ValCtx
.

Arguments c_hole {_}{_}.
Arguments c_app1 {_}{_}{_}.
Arguments c_app2 {_}{_}{_}.
Arguments c_let1 {_}{_}{_}.
Arguments c_let2 {_}{_}{_}.
Arguments c_ifz1 {_}{_}{_}.
Arguments c_ifz2 {_}{_}{_}.
Arguments c_ifz3 {_}{_}{_}.
Arguments c_ret {_}{_}{_}.
Arguments v_abs {_}{_}{_}.
Arguments v_succ {_}{_}{_}.

Local Notation "#" := c_hole (at level 7).

(* Do this in interactive mode to make working with the dependent types
   easier. But don't automate too much to make sure that we get the 
   arguments in the right order in app/case/prod *)
Fixpoint plug {m}{n}{T1 T2 : ContextType} (C : Context m n T1 T2) : CT T1 m -> CT T2 n.
destruct C.
all: intros e.
- eapply e.
- eapply (app (plug _ _ _ _ C e) v). 
- eapply (app v (plug _ _ _ _ C e)).
- eapply (let_ (plug _ _ _ _ C e) t).
- eapply (let_ t (plug _ _ _ _ C e)).
- eapply (ifz (plug _ _ _ _ C e) t t0).
- eapply (ifz v (plug _ _ _ _ C e) t).
- eapply (ifz v t (plug _ _ _ _ C e)).
- eapply (ret (plug _ _ _ _ C e)).
- eapply (abs (plug _ _ _ _ C e)).
- eapply (succ (plug _ _ _ _ C e)).
Defined.

Notation "C {| e |} " := (plug C e). 

Fixpoint compose {m n p}{T1 T2 T3} (C1 : Context m n T1 T2) (C2 : Context n p T2 T3) : Context m p T1 T3.
- dependent destruction C2.
  + exact C1.
  + eapply c_app1; eauto.
  + eapply c_app2; eauto.
  + eapply c_let1; eauto.
  + eapply c_let2; eauto.
  + eapply c_ifz1; eauto.
  + eapply c_ifz2; eauto.
  + eapply c_ifz3; eauto.
  + eapply c_ret; eauto.
  + eapply v_abs; eauto.
  + eapply v_succ; eauto.
Defined.

Infix "∘" := compose (at level 70).

Fixpoint compose_plug  {m n p T1 T2 T3} (C1 : Context m n T1 T2) (C2 : Context n p T2 T3) e : 
  C2 {| C1 {| e |} |} = (C1 ∘ C2) {| e |}.
Proof.
  dependent destruction C2.
  all: cbn.
  all: try (rewrite compose_plug; done).
  done.
Qed.

Reserved Notation "C ∈C Γ ▷ τ ⤳ Δ ▷ τ'" (at level 70).

Inductive typing_Context m (Γ : Ctx m) (τ : Ty 0) : forall n (Δ : Ctx n) (τ' : Ty 0) T1 T2, Context m n T1 T2 -> Prop :=
  | ctx_hole T : (@c_hole _ T) ∈C Γ ▷ τ ⤳ Γ ▷ τ
  | ctx_app1 m (Δ : Ctx m) τ1 τ2  T1 C v : 
    (C ∈C Γ ▷ τ ⤳ Δ ▷ Arr τ1 τ2) ->
    (Δ |-v v ∈ τ1) ->
    (@c_app1 _ _ T1 C v) ∈C Γ ▷ τ ⤳ Δ ▷ τ2
 | ctx_app2  m (Δ : Ctx m) τ1 τ2  T1 C v : 
    (Δ |-v v ∈ Arr τ1 τ2) ->
    (C ∈C Γ ▷ τ ⤳ Δ ▷ τ1) ->
    (@c_app2 _ _ T1 v C) ∈C Γ ▷ τ ⤳ Δ ▷ τ2
 | ctx_let1  m (Δ : Ctx m) τ1 τ2  T1 C e : 
    (C ∈C Γ ▷ τ ⤳ Δ ▷ τ1) ->
    (τ1 .: Δ |-e e ∈ τ2) ->
    (@c_let1 _ _ T1 C e) ∈C Γ ▷ τ ⤳ Δ ▷ τ2
 | ctx_let2  m (Δ : Ctx m) τ1 τ2  T1 C e : 
    (Δ |-e e ∈ τ1) ->
    (C ∈C  Γ ▷ τ ⤳ τ1 .: Δ ▷ τ2) ->
    (@c_let2 _ _ T1 e C) ∈C Γ ▷ τ ⤳ Δ ▷ τ2
 | ctx_ret   m (Δ : Ctx m) τ1 T1 C : 
    (C ∈C Γ ▷ τ ⤳ Δ ▷ τ1) -> 
    (@c_ret _ _ T1 C) ∈C Γ ▷ τ ⤳ Δ ▷ τ1
 | ctx_abs   m (Δ : Ctx m) τ1 τ2 T1 C : 
    (C ∈C Γ ▷ τ ⤳ τ1 .: Δ ▷ τ2) -> 
    (@v_abs _ _ T1 C) ∈C Γ ▷ τ ⤳ Δ ▷ Arr τ1 τ2

where 
    "C ∈C Γ ▷ τ ⤳ Δ ▷ τ'" := (typing_Context _ Γ τ _ Δ τ' _ _ C).



(** * "Contextual Equivalence" *)
Definition Contextual (n : nat) Γ (e1 : Tm n) (e2 : Tm n) τ :=
    Γ |-e e1 ∈ τ /\
    Γ |-e e2 ∈ τ /\ 
  forall (C :Context n 0 TmCtx TmCtx), 
    C ∈C Γ ▷ τ ⤳ null ▷ Nat -> 
       exists n, (nil, C {|e1|}) ↦* (nil, ret n) /\ (nil, C{|e2|}) ↦* (nil, ret n).
Definition ContextualVal (n : nat) Γ (v1 : Val n) (v2 : Val n) τ := 
  Γ |-v v1 ∈ τ /\
  Γ |-v v2 ∈ τ /\ 
  forall (C :Context n 0 ValCtx TmCtx), 
    C ∈C Γ ▷ τ ⤳ null ▷ Nat -> 
       exists n, (nil, C {|v1|}) ↦* (nil, ret n) /\ (nil, C{|v2|}) ↦* (nil, ret n).

Instance Adequate_Contextual : Adequate Contextual.
Proof.
  unfold Adequate.
  intros e e' C.
  unfold Contextual in C.
  move: C => [T1 [T2 C]].
  specialize (C #).
  cbn in C.
  asimpl in C.
Admitted.

Lemma Transitive_Contextual : ScopedTransitive Contextual.
Proof.
  intros n e1 e2 e3 CT1 CT2 C h.
  unfold Contextual in CT1, CT2.
  eauto.
Qed.

(** If two terms are contextually related, then any larger terms from plugging 
    them into a context are also related. *)
Lemma Contextual_Replacement n e1 e2 : 
  Contextual n e1 e2 -> 
  forall m (C : Context n m TmCtx TmCtx), Contextual m (C{| e1 |}) (C{| e2|}).
Proof.
  intros h m C.
  unfold Contextual in *.
  intros C0. 
  repeat rewrite compose_plug.
  eapply h.
Qed.

Ltac compose_rewrite C1 := 
  repeat rewrite <- compose_plug in C1; cbn in C1; asimpl in C1; auto.

Instance Compatible_Contextual : Compatible Contextual ContextualVal.
split.
all: intros n.
all: repeat unfold Contextual, ContextualVal.
- intros x C. intro h. done.
- intros C. done.
- intros C. done.
- (* succ *)
  intros v1 v2 C1 C h.
  specialize (@C1 (v_succ # ∘ C)).
  compose_rewrite C1.

- (* abs *)
  intros e1 e2 C1 C h.
  specialize (@C1 (v_abs # ∘ C)).
  compose_rewrite C1.

- (* ret *)
  intros v1 v2 C1 C h.
  specialize (@C1 (c_ret # ∘ C)).
  compose_rewrite C1.
- (* let *) 
  intros e1 e2 e1' e2' C1 C2 C h.
  specialize (@C2 (c_let2 e2 # ∘ C)).
  compose_rewrite C2.
  specialize (@C1 (c_let1 # e1' ∘ C)).
  compose_rewrite C1.
- (* ifz *)
  intros v1 v2 e1 e2 e1' e2' C1 C2 C3 C h.
  specialize (@C3 (c_ifz3 v1 e1 # ∘ C)).
  compose_rewrite C3.
  specialize (@C2 (c_ifz2 v1 # e2' ∘ C)).
  compose_rewrite C2.
  specialize (@C1 (c_ifz1 # e2 e2' ∘ C)).
  compose_rewrite C1.

- (* app *)
  intros v1 v2 v1' v2' C1 C2 C.
  specialize (@C2 (c_app2 v2 # ∘ C)).
  compose_rewrite C2.
  specialize (@C1 (c_app1 # v1' ∘ C)).
  compose_rewrite C1.

Qed.

(** * Contextual equivalence implies CTX *)
Lemma Contextual_CTX n e1 e2 : Contextual n e1 e2 -> CTX n e1 e2.
Proof.
  intro h. 
  exists Contextual ContextualVal; eauto.
  eapply Compatible_Contextual.
  eapply Adequate_Contextual.
  eapply Transitive_Contextual.
Qed.


(* ---------------------------------------------------- *)

(** * If RE is a compatible relation and relates two terms, then it 
      also related the terms in an arbitrary context *)
Fixpoint Compatible_plug n (e1 e2 : Tm n) 
  (RE : scoped_relation Tm)
  (RV : scoped_relation Val)
  (H : Compatible RE RV) :
  RE n e1 e2 -> forall m (C : Context n m TmCtx TmCtx),
  RE m C {|e1|} C {|e2|} 
with 
  Compatible_vplug n (e1 e2 : Tm n) 
  (RE : scoped_relation Tm)
  (RV : scoped_relation Val)
  (H : Compatible RE RV) :
  RE n e1 e2 -> forall m (C: Context n m TmCtx ValCtx),
  RV m (C {|e1|}) (C{|e2|}).
Proof.
- intros h m C.
  dependent destruction C.
  all: cbn.
  all: specialize (Compatible_plug n e1 e2 RE RV H h).
  all: specialize (Compatible_vplug n e1 e2 RE RV H h).
  + auto.
  + eapply comp_app. 
    eapply Compatible_vplug; eauto.
    eapply scoped_refl. typeclasses eauto.
  + eapply comp_app. eapply scoped_refl. typeclasses eauto.
    eapply Compatible_vplug; eauto.
  + eapply comp_let. eapply Compatible_plug; eauto.
    eapply scoped_refl. typeclasses eauto.
  + eapply comp_let. 
    eapply scoped_refl. typeclasses eauto.
    eapply Compatible_plug.
  + eapply comp_ifz.
    eapply Compatible_vplug.
    eapply scoped_refl. typeclasses eauto.
    eapply scoped_refl. typeclasses eauto.
  + eapply comp_ifz.
    eapply scoped_refl. typeclasses eauto.
    eapply Compatible_plug.
    eapply scoped_refl. typeclasses eauto.
  + eapply comp_ifz.
    eapply scoped_refl. typeclasses eauto.
    eapply scoped_refl. typeclasses eauto.
    eapply Compatible_plug.
  + eapply comp_ret. 
    eapply Compatible_vplug.

- intros h m C.
  dependent destruction C.
  all: cbn.
  all: specialize (Compatible_plug n e1 e2 RE RV H h).
  all: specialize (Compatible_vplug n e1 e2 RE RV H h).
  + eapply val_abs. eauto.
  + eapply val_succ. eauto.

Qed.

(** * CTX implies Contextual *)
Lemma CTX_Contextual n e1 e2 : 
  CTX n e1 e2 -> Contextual n e1 e2.
Proof.
  intro h. 
  unfold Contextual.
  intros C.
  destruct h.
  eapply H0.
  eapply Compatible_plug; eauto.
Qed.

*)




(** ------------------------------------------------- *)

(** * CIU_equivalence on typed terms *)

Definition CIU : typed_relation Tm := 
  fun n Γ e e' τ =>  
         Γ |-e e ∈ τ /\
         Γ |-e e' ∈ τ /\
    forall σ, typing_subst null σ Γ -> 
    forall s, typing_stack s τ Nat -> 
         nat_equiv (s, e[σ]) (s, e'[σ]).

Instance TypedRelation_CIU : TypedRelation Tm (@typing) CIU.
split; intros; inversion H; inversion H1; eauto.
Qed.

Instance Reflexive_CIU : TypedReflexive (@typing) CIU.
intros n Γ e τ h.
unfold CIU. repeat split; eauto; reflexivity.
Qed.

Instance Transitive_CIU : TypedTransitive CIU.
Proof.
  intros n Γ t1 t2 t3 τ.
  unfold CIU.
  intros [T1 [T1' h1]] [T2 [T2' h2]]. 
  split. eauto.
  split. eauto.
  intros.
  specialize (h1 σ H s H0).
  specialize (h2 σ H s H0).
  transitivity (s, t2[σ]); eauto.
Qed.


Instance Adequate_CIU : Adequate CIU.
Proof.
  intros e e' h.
  destruct h as [T1 [T2 h]].
  specialize (h var ltac:(eauto with rec) nil (st_nil Nat)).
  asimpl in h.
  auto.
Qed.

(** * Logical relation definition of Equivalence *)


Fixpoint eqnat (v1 : Val 0) (v2 : Val 0) : Prop := 
  match v1 , v2 with 
    | zero, zero => True
    | succ v1, succ v2 => eqnat v1 v2
    | _,_ => False
  end.

Lemma eqnat_refl : forall v, null |-v v ∈ Nat -> eqnat v v.
Proof. intros v h. dependent induction h.
       destruct x0. cbn. done. cbn. eauto.
Qed.

Lemma eqnat_sound v1 v2 : eqnat v1 v2 -> v1 = v2.
Proof.
  move: v2. dependent induction v1.
  all: intros v2 h. 
  all: destruct v2; try done.
  f_equal.
  apply IHv1; eauto.
Qed.


Lemma eqnat_typed1 v1 v2 : eqnat v1 v2 -> null |-v v1 ∈ Nat.
  move: v2. dependent induction v1.
  all: intros v2 h.
  all: destruct v2; try done.
  all: eauto with rec.
Qed.

Lemma eqnat_typed2 v1 v2 : eqnat v1 v2 -> null |-v v2 ∈ Nat.
  move: v2. dependent induction v1.
  all: intros v2 h.
  all: destruct v2; try done.
  all: eauto with rec.
Qed.


(** * A typed logical relation *)

Fixpoint V (τ : Ty 0) {struct τ} : Val 0 -> Val 0 -> Prop :=
  let St (τ : Ty 0) (s s' : stack) := 
  typing_stack s τ Nat /\
  typing_stack s' τ Nat /\ 
  (forall v v', V τ v v' -> (s, ret v) ≡ℕ (s', ret v')) in
  let C (τ : Ty 0) (e e' : Tm 0) := 
  typing null e τ /\
  typing null e' τ /\ 
  forall s s', St τ s s' -> (s,e) ≡ℕ (s',e') in
  match τ with
  | Nat => eqnat
  | Unit => fun v1 v2 => null |-v v1 ∈ Unit /\ null |-v v2 ∈ Unit
  | Arr τ1 τ2 => fun v1 v2 =>
      match v1, v2 with 
      | abs e1, abs e2 => 
         τ1 .: null |-e e1 ∈ τ2 /\
         τ1 .: null |-e e2 ∈ τ2 /\ 
         forall w1 w2, V τ1 w1 w2 -> 
                  C τ2 (e1[w1..]) (e2[w2..])
      | _, _ => False
      end
  | _ => fun v1 v2 => False
  end.

Definition St (τ : Ty 0) (s s' : stack) := 
    typing_stack s τ Nat  /\
    typing_stack s' τ Nat /\ 
    forall v v', V τ v v' -> (s, ret v) ≡ℕ (s', ret v').

Definition C (τ : Ty 0) (e e' : Tm 0) := 
  typing null e τ /\
  typing null e' τ /\ 
  forall s s', St τ s s' -> (s,e) ≡ℕ (s',e').


Lemma V_typed1 {τ v1 v2} : V τ v1 v2 -> null |-v v1 ∈ τ.
Proof.
  intros h.
  destruct τ.
  all: cbn in h; try done.
  all: destruct v1; destruct v2; try done.
  all: try destruct h.
  all: try invert_typing.
  all: eauto with rec.
  - eapply eqnat_typed1; eauto.
Qed.

Lemma V_typed2 {τ v1 v2} : V τ v1 v2 -> null |-v v2 ∈ τ.
Proof.
  intros h.
  destruct τ.
  all: cbn in h; try done.
  all: destruct v1; destruct v2; try done.
  all: try destruct h.
  all: try invert_typing.
  all: eauto with rec.
  - eapply eqnat_typed2; eauto.
  - move: H0 => [hT2 h].
    econstructor; eauto with rec.
Qed.


Lemma St_def τ s s' : 
  St τ s s' -> forall v v', V τ v v' -> (s, ret v) ≡ℕ (s', ret v').
Proof.
intros. destruct H as [T1 [T2 H]].  eauto.
Qed.

Lemma C_def (τ : Ty 0) (e e' : Tm 0) : 
  C τ e e' ->
  forall s s', St τ s s' -> (s,e) ≡ℕ (s',e').
Proof.
  intros [_ [_ h]]. done. 
Qed. 


Lemma St_nil : St Nat nil nil.
Proof.
split. eauto with rec.
split. eauto with rec.
intros v v' Vv.
apply eqnat_sound in Vv. subst. reflexivity.
Qed.

(** Lifting the logical relation to open terms *)

Definition log_sig n Γ (σ σ' : fin n -> Val 0) :=
    forall x, V (Γ x) (σ x) (σ' x).

Definition log_val n Γ (v v' : Val n) τ := 
  Γ |-v v ∈ τ /\
  Γ |-v v' ∈ τ /\
  forall σ σ' , log_sig n Γ σ σ' -> V τ v[σ] v'[σ'].

Definition log_tm  n Γ (e e' : Tm n) τ := 
  Γ |-e e ∈ τ /\
  Γ |-e e' ∈ τ /\
  forall σ σ' , log_sig n Γ σ σ' -> C τ e[σ] e'[σ'].
  
Instance TypedRelation_log_val : TypedRelation Val (@typing_val) log_val.
split.
intros. destruct H as [T1 [T2 h]]. done.
intros. destruct H as [T1 [T2 h]]. done.
Qed.

Instance TypedRelation_log_tm : TypedRelation Tm (@typing) log_tm.
split.
intros. destruct H as [T1 [T2 h]]. done.
intros. destruct H as [T1 [T2 h]]. done.
Qed.

Lemma log_sig_typed1 {n Γ σ σ'} : log_sig n Γ σ σ' -> typing_subst null σ Γ.
intro h. unfold log_sig, typing_subst in *.
intro x. specialize (h x). eapply V_typed1 in h; eauto.
Qed.

Lemma log_sig_typed2 {n Γ σ σ'} : log_sig n Γ σ σ' -> typing_subst null σ' Γ.
intro h. unfold log_sig, typing_subst in *.
intro x. specialize (h x). eapply V_typed2 in h; eauto.
Qed.

Lemma reverse_prim2 τ e1  e2 e2' : 
  C τ e1 e2' -> null |-e e2 ∈ τ -> e2 ~>> e2' -> C τ e1 e2.
Proof.
  unfold C.
  intros [h1[h2 h]] hSS1 .
  split. eauto with rec.
  split. eauto with rec.
  intros s s' Sts.
  specialize (h _ _ Sts).
  transitivity (s', e2'); eauto.
  symmetry.
  eapply nat_step. 
  eapply StackSmall.s_prim; eauto. 
Qed.

Lemma reverse_prim1 τ e1 e1' e2  : 
  C τ e1' e2 -> null |-e e1 ∈ τ -> e1 ~>> e1' -> C τ e1 e2.
Proof.
  unfold C.
  intros [h1 [h2 h]] hT hSS1.
  split. eauto with rec.
  split. eauto with rec.
  intros s s' Sts.
  specialize (h _ _ Sts).
  transitivity (s, e1'); eauto.
  eapply nat_step.
  eapply StackSmall.s_prim; eauto. 
Qed.

Lemma C_app τ1 τ2 v1 v1' v2 v2' :
  V (Arr τ1 τ2) v1 v1' ->
  V τ1 v2 v2' ->
  C τ2 (app v1 v2) (app v1' v2').
Proof.
  move=> h1 h2.
  destruct v1; try done.
  destruct v1'; try done.
  cbn in h1.
  move: h1 => [T1 [T2 h1]].
  eapply reverse_prim1. 
  2: { econstructor; eauto using V_typed1 with rec.  } 
  2: { eapply s_beta; eauto. } 
  eapply reverse_prim2.
  2: { econstructor; eauto using V_typed2 with rec. } 
  2: { eapply s_beta; eauto. } 
  split; eauto using V_typed1 with rec.
  split; eauto using V_typed2 with rec.
  intros s s' [ST1 [S2 Sts]].
  eapply h1; eauto.
Qed.


(** * Compatibility rules: values *)

Section Compatibility.

Context (n:nat)(Γ : Ctx n).

Lemma log_var x : log_val n Γ (var x) (var x) (Γ x).
Proof.
split; eauto with rec.
Qed.

Lemma log_zero : log_val n Γ zero zero Nat.
Proof.
split; eauto with rec.
split; eauto with rec.
intros σ σ' Es.
cbn. done.
Qed.

Lemma log_unit : log_val n Γ unit unit Unit.
Proof.
split; eauto with rec.
split; eauto with rec.
intros σ σ' Es.
cbn. split; eauto with rec.
Qed.

Lemma log_succ v v' : 
  log_val n Γ v v' Nat -> 
  log_val n Γ (succ v) (succ v') Nat.
Proof.
intros [T1 [T2 h]].
split; eauto with rec.
Qed.

Lemma log_abs  e e' τ1 τ2 : 
  log_tm (S n) (τ1 .: Γ) e e' τ2 ->
  log_val n Γ (abs e) (abs e') (Arr τ1 τ2).
Proof.
intros [T1 [T2 h]].
split; eauto with rec.
split; eauto with rec.
intros σ σ' Es.
move: (log_sig_typed1 Es) => ST1.
move: (log_sig_typed2 Es) => ST2.
cbn.
split. eauto with rec. 
split. eauto with rec.
intros v v' Vv.
asimpl.
move: (V_typed1 Vv) => VT1.
move: (V_typed2 Vv) => VT2.
split; eauto with rec.
split; eauto with rec.
intros s s' [sT1 [sT2 h1]].
eapply h.
unfold log_sig. auto_case.
unfold St.
split. auto.
split. auto.
eauto.
Qed.

Lemma log_ret v v' τ : 
  log_val n Γ v v' τ  ->
  log_tm n Γ (ret v) (ret v') τ.
Proof.
  intros [T1 [T2 h]].
  split; eauto with rec.
  split; eauto with rec.
  cbn.
  intros σ σ' Es.
  specialize (h σ σ' Es).
  move: (V_typed1 h) => Tv1.
  move: (V_typed2 h) => Tv2.
  split; eauto with rec.
  split; eauto with rec.
  intros s s' [ST1 [ST2 Sts]].
  eapply Sts; eauto.
Qed.

Lemma log_let e1  e1' e2 e2' τ1 τ2 :
  log_tm n Γ e1 e1' τ1 -> 
  log_tm (S n) (τ1 .: Γ) e2 e2' τ2 -> 
  log_tm n Γ (let_ e1 e2) (let_ e1' e2') τ2.
Proof.
  intros [T1 [T1' h1]].
  intros [T2 [T2' h2]].
  split; eauto with rec.
  split; eauto with rec.
  intros σ σ' Lσ. cbn.
  specialize (h1 σ σ' Lσ).
  move: h1 => [_ [_ h1]].
  move: (log_sig_typed1 Lσ) => Tσ.
  move: (log_sig_typed2 Lσ) => Tσ'.
  split; eauto with rec.
  split; eauto with rec.
  intros s s' [Ts [Ts' Sts]].
  transitivity (f_let e2[⇑σ] :: s, e1[σ]).
  { eapply nat_step. eapply StackSmall.s_push. } 
  transitivity (f_let e2'[⇑σ'] :: s', e1'[σ']).
  2: { symmetry. eapply nat_step. eapply StackSmall.s_push. }
  eapply h1.
  split; eauto with rec.
  split; eauto with rec.
  intros v v' Vv.
  transitivity (s, e2[v .: σ]).
  { eapply nat_multi. eapply ms_trans. eapply StackSmall.s_pop. 
    asimpl. eapply ms_refl. } 
  transitivity (s', e2'[v' .: σ']).
  2: { symmetry. eapply nat_multi. eapply ms_trans. eapply StackSmall.s_pop. 
    asimpl. eapply ms_refl. } 
  eapply h2; eauto.
  unfold log_sig; auto_case.
  split; eauto.
Qed.

Lemma log_app e1 e1' e2 e2' τ1 τ2 : 
  log_val n Γ e1 e1' (Arr τ1 τ2) -> 
  log_val n Γ e2 e2' τ1 -> 
  log_tm n Γ (app e1 e2) (app e1' e2') τ2.
Proof.
  intros [T1 [T1' h1]].
  intros [T2 [T2' h2]].
  split; eauto with rec.
  split; eauto with rec.
  intros σ σ' Lσ. cbn.
  specialize (h1 σ σ' Lσ).
  specialize (h2 σ σ' Lσ).
  eapply C_app; eauto.
Qed.

Lemma log_ifz v v' e0 e0' e1 e1' τ : 
  log_val n Γ v v' Nat -> 
  log_tm n Γ e0 e0' τ -> 
  log_tm _ (Nat .: Γ) e1 e1' τ ->
  log_tm n Γ (ifz v e0 e1) (ifz v' e0' e1') τ.
Proof.
  intros [Tv [Tv' h1]].
  intros [Te0 [Te0' h2]].
  intros [Te1 [Te1' h3]].
  split; eauto with rec.
  split; eauto with rec.
  intros σ σ' Lσ.
  specialize (h1 σ σ' Lσ).
  move: (log_sig_typed1 Lσ) => Tσ.
  move: (log_sig_typed2 Lσ) => Tσ'.
  cbn. 
  destruct v[σ] eqn:E1;
  destruct v'[σ'] eqn:E2;
  cbn in h1; try done;
  auto_unfold in *; rewrite E1; rewrite E2.
  - eapply reverse_prim1; eauto with rec.
    eapply reverse_prim2; eauto with rec.
    eapply s_ifz_zero.
    eapply s_ifz_zero.
  - apply eqnat_sound in h1. subst.
    have Tvs: null |-v v[σ] ∈ Nat. eauto with rec.
    auto_unfold in *. rewrite E1 in Tvs. inversion Tvs. subst.
    eapply reverse_prim1; eauto with rec.
    2: { eapply s_ifz_succ. } 
    eapply reverse_prim2; eauto with rec.
    2: { eapply s_ifz_succ. } 
    asimpl.
    eapply h3.
    unfold log_sig. auto_case.
    eapply eqnat_refl; eauto.
Qed.
  
End Compatibility.

Instance compat_log : Compatible log_tm log_val.
constructor.
- eapply log_var.
- eapply log_unit.
- eapply log_zero.
- eapply log_succ.
- eapply log_abs.
- eapply log_ret.
- eapply log_let.
- eapply log_ifz.
- eapply log_app.
Qed.


Corollary refl_val {n Γ v τ} : Γ |-v v ∈ τ -> log_val n Γ v v τ.
intros h. eapply Compatible_refl_RV; eauto using compat_log. Qed.
Corollary refl_tm {n Γ e τ} : Γ |-e e ∈ τ -> log_tm n Γ e e τ.
intros h. eapply Compatible_refl_RE; eauto using compat_log. Qed.


Lemma refl_sig {n Γ s} : typing_subst null s Γ -> 
                       log_sig n Γ s s.
Proof.
intros TS.
unfold log_sig. 
intros x.
move: (refl_val (TS x)) => h.
unfold log_val in h.
move: h => [T1 [T2 h]].
specialize (h ids ids). asimpl in h.
eapply h.
unfold log_sig. auto_case.
Qed.


Lemma St_cons f s1 s2 τ1 τ2 : 
  typing_frame f τ1 τ2 ->
  St τ2 s1 s2 ->
  St τ1 (f :: s1) (f :: s2).
Proof.
  intros h1 [ST1 [ST2 h2]].
  inversion h1; subst; clear h1.
  split; eauto with rec. 
  split; eauto with rec.
  move: (refl_tm H) => [_ [_ h1]].
  intros v1 v1' VV.
  transitivity (s1, e1[v1 ..]).
  { eapply nat_step. eapply StackSmall.s_pop. } 
  transitivity (s2, e1[v1' ..]).
  { eapply h1. unfold log_sig. auto_case. destruct f. 
    split; eauto. } 
  symmetry.
  { eapply nat_step. eapply StackSmall.s_pop. } 
Qed.


Lemma refl_St s τ1 : typing_stack s τ1 Nat -> St τ1 s s.
Proof.
move: τ1.
induction s; intros.
inversion H.
eapply St_nil.
inversion H; subst.
eapply St_cons; eauto.
Qed.


(* --------------------------------------------- *)
(*** log <-> CIU *)

Lemma log_tm_CIU n (Γ : Ctx n) e e' τ : 
  log_tm n Γ e e' τ -> CIU n Γ e e' τ.
Proof.
  intros [T1 [T2 h]].
  split; auto.
  split; auto.
  intros s Ts E TE. 
  have ES: log_sig n Γ s s. eapply refl_sig; eauto. 
  specialize (h _ _ ES).
  have EE: St τ E E. eapply refl_St; eauto. 
  move: h => [T1' [T2' h]].
  eapply h; eauto.
Qed.


(* Logical equivalence is closed under CIU *)
Lemma log_tm_closed_CIU n (Γ : Ctx n) e e' e'' τ :
  log_tm n Γ e e' τ -> CIU n Γ e' e'' τ -> log_tm n Γ e e'' τ.
Proof. 
  intros [T1 [T2 h1]] [_ [T3 h2]].
  split; eauto.
  split; eauto.
  intros s s' hs.
  specialize (h1 s s' hs).
  move: (log_sig_typed2 hs) => ST2.
  specialize (h2 s' ST2).
  move: h1 => [T1' [T2' h1]].
  split; eauto.
  split; eauto with rec.
  intros E E' StEj.   
  specialize (h1 E E' StEj).  
  transitivity (E', e'[s']); eauto.
  eapply h2.
  destruct StEj as [_ [h3 _]]. 
  done.
Qed.

Lemma CIU_log_tm {n Γ e e' τ} : 
  CIU n Γ e e' τ -> log_tm n Γ e e' τ.
Proof.
  intros [T1 [T2 h]].
  move: (refl_tm T1) => hE.
  eapply log_tm_closed_CIU; eauto.
  split; eauto.
Qed.

(* --------------------------------------------- *)
(*** CIU -> CTX *)


Instance Compatible_CIU : Compatible CIU log_val.
constructor.
- eapply log_var; eauto.
- eapply log_unit; eauto.
- eapply log_zero; eauto.
- eapply log_succ; eauto.
- intros n Γ e1 e2 τ1 τ2 CIU1.
  eapply log_abs.
  eapply CIU_log_tm; auto.
- intros.
  eapply log_tm_CIU.
  eapply log_ret; eauto.
- intros.
  eapply log_tm_CIU.
  eapply log_let; eauto using CIU_log_tm.
- intros. 
  eapply log_tm_CIU.
  eapply log_ifz; eauto using CIU_log_tm.
- intros.
  eapply log_tm_CIU.
  eapply log_app; eauto.
Qed.


Lemma CIU_CTX n (Γ : Ctx n) e e' τ : 
  CIU n Γ e e' τ -> CTX n Γ e e' τ.
Proof.
  intros h.
  econstructor; eauto.
  - eapply Compatible_CIU.
  - eapply Adequate_CIU.
  - eapply Transitive_CIU.
  - eapply TypedRelation_CIU.
  - eapply TypedRelation_log_val.
Qed.

(* -------------------------------------------- *)
(*** CTX -> CIU *)


Lemma substitutivity { n Γ e e' v τ1 τ2} : 
  CTX (S n) (τ1 .: Γ) e e' τ2 ->
  typing_val Γ v τ1 ->
  CTX n Γ e[v..] e'[v..] τ2.
Proof.
  intros h Tv.
  have Te: (τ1 .: Γ) |-e e ∈ τ2. { inversion h. eapply typed1; eauto. } 
  have Te': (τ1 .: Γ) |-e e' ∈ τ2. { inversion h. eapply typed2; eauto. } 
  have C1: CTX n Γ (let_ (ret v) e) (let_ (ret v) e') τ2.
  { 
    destruct h.
    econstructor; eauto.
    eapply comp_let.
    eapply comp_ret.
    eapply Compatible_refl_RV; eauto.
    assumption.
  } 
  have C2 : CTX n Γ e[v..] (let_ (ret v) e) τ2.
  { 
    eapply CIU_CTX.
    split; eauto with rec.
    split; eauto with rec.
    intros σ Tσ s Ts.
    asimpl.
    symmetry.
    eapply nat_multi.
    eapply ms_trans.
    eapply StackSmall.s_push.
    eapply ms_trans.
    eapply StackSmall.s_pop.
    asimpl.
    eapply ms_refl.
  } 
  have C3 : CTX n Γ (let_ (ret v) e') e'[v..] τ2.
  { 
    eapply CIU_CTX.
    split; eauto with rec.
    split; eauto with rec.
    intros σ Tσ s Ts.
    asimpl.
    eapply nat_multi.
    eapply ms_trans.
    eapply StackSmall.s_push.
    eapply ms_trans.
    eapply StackSmall.s_pop.
    asimpl.
    eapply ms_refl.
  } 
  eapply Transitive_CTX; eauto. 
  eapply Transitive_CTX; eauto.
Qed.

Lemma CTX_CIU_closed {e e' τ} :
  CTX 0 null e e' τ -> CIU 0 null e e' τ.
Proof. 
  intros h.
  inversion h. clear h.
  split. eapply typed1; eauto.
  split. eapply typed2; eauto.
  intros σ Tσ s Ts.
  auto_unfold in *. repeat rewrite idSubst_Tm. auto_case. auto_case.
  clear σ Tσ.
  move: τ Ts e e'  H4.
  induction s; intros τ Ts e e' Re.
  - inversion Ts. subst. 
    eapply H0 in Re.
    done.
  - destruct a.
    transitivity (s, let_ e t).
    { symmetry. eapply nat_step. eapply StackSmall.s_push. } 
    transitivity (s, let_ e' t).
    2:{ eapply nat_step. eapply StackSmall.s_push. }
    repeat invert_typing.
    eapply IHs; eauto.
    eapply comp_let; eauto.
    eapply Compatible_refl_RE; eauto.
Qed.

Lemma split_sigma (n : nat) (e : Tm (S n)) (σ : fin (S n) -> Val 0) :
  e[(σ var_zero)⟨null⟩..][↑ >> σ] = e[σ].
Proof. 
  asimpl.
  rewrite idSubst_Val. auto_case.
  asimpl.
  auto.
Qed.


Lemma value_substitutivity n Γ e e' τ : 
  CTX n Γ e e' τ -> 
  forall σ, typing_subst null σ Γ -> CTX 0 null e[σ] e'[σ] τ.
Proof.
  move: Γ e e' τ.
  induction n.
  all: intros Γ e e' τ h σ σT.
  - auto_unfold. 
    have EQ: (Γ = null).
    { eapply functional_extensionality. auto_case.   } 
    rewrite EQ in h.
    repeat rewrite idSubst_Tm; try auto_case. auto.
  - remember ((σ var_zero)⟨null⟩ : Val n) as v.
    have EQΓ: Γ = (Γ var_zero .: ↑ >> Γ ).
    { eapply functional_extensionality. auto_case. }
    rewrite EQΓ in h, σT.
    have EQσ: σ = (σ var_zero .: ↑ >> σ ).
    { eapply functional_extensionality. auto_case. }
    rewrite EQσ in σT.
    unfold typing_subst in σT.
    specialize (IHn (↑ >> Γ) e[v..] e'[v..] τ).
    have h1:  CTX n (↑ >> Γ) e[v..] e'[v..] τ.
    { eapply substitutivity; eauto. 
      specialize (σT var_zero). cbn in σT.
      rewrite Heqv.
      eapply renaming_val; eauto.
      unfold typing_renaming. auto_case.
    }
    specialize (IHn h1 (↑ >> σ)).
    rewrite Heqv in IHn.
    repeat rewrite split_sigma in IHn.
    eapply IHn.
    unfold typing_subst. intro x.
    specialize (σT (Some x)). cbn in σT.
    done.
Qed.


Lemma CTX_CIU n Γ e e' τ :
  CTX n Γ e e' τ -> CIU n Γ e e' τ.
Proof. 
  intros h.
  unfold CIU.
  destruct (TypedRelation_CTX) as [typed1 typed2].
  split. eapply typed1; eauto.
  split. eapply typed2; eauto.
  intros σ Tσ s Ts.
  eapply value_substitutivity with (σ := σ) in h. 2: eassumption.
  move: (CTX_CIU_closed h) => [_ [_ h1]].
  have Tnull: typing_subst null null null. eapply typing_subst_null.
  specialize (h1 null Tnull s Ts).
  auto_unfold in *. rewrite idSubst_Tm in h1. auto_case. rewrite idSubst_Tm in h1. auto_case.
  auto.
Qed.


(* -------------------------------------------- *)


(*** Examples: Beta-equiv *)

Lemma s_prim' : 
  forall s e e1 e2, e ~>> e1 -> e1 = e2 -> (s, e) ↦ (s, e2). 
Proof.
  intros. eapply StackSmall.s_prim. subst. auto.
Qed.

Lemma fun_beta :
  forall n Γ e v τ , 
    Γ |-e (app (abs e) v) ∈ τ -> 
       CIU n Γ (app (abs e) v) e[v..] τ.
Proof.
  intros.
  unfold CIU. 
  split. auto.
  split. inversion H; subst. inversion H2; subst. eapply substitution_tm; eauto using typing_subst_cons, typing_subst_id.
  intros σ Tσ s Ts.
  cbn. 
  eapply nat_step.
  eapply s_prim'.
  eapply s_beta.
  asimpl.
  done.
Qed.

Lemma let_beta n Γ e v τ : 
    Γ |-e let_ (ret v) e ∈ τ -> 
       CIU n Γ (let_ (ret v) e) e[v..] τ.
Proof.
  intro h.
  inversion h; subst. inversion H1; subst.
  unfold CIU.
  split; auto.
  split. eapply substitution_tm; eauto using typing_subst_cons, typing_subst_id.
  intros σ Tσ s Ts.
  cbn. asimpl.
  eapply nat_multi.
  eapply ms_trans.
  eapply StackSmall.s_push.
  eapply ms_trans.
  eapply StackSmall.s_pop.
  asimpl.
  eapply ms_refl.
Qed.

Lemma ifz_zero_beta n Γ e0 e1  τ : 
    Γ |-e ifz zero e0 e1 ∈ τ -> 
       CIU n Γ (ifz zero e0 e1) e0 τ.
Proof.
  intro h.
  inversion h; subst. 
  unfold CIU.
  split; auto.
  split; auto. 
  intros σ Tσ s Ts.
  cbn. asimpl.
  eapply nat_step.
  eapply StackSmall.s_prim.
  eapply s_ifz_zero.
Qed.

Lemma ifz_succ_beta n Γ v e0 e1 τ : 
    Γ |-e ifz (succ v) e0 e1 ∈ τ -> 
       CIU n Γ (ifz (succ v) e0 e1) e1[v..] τ.
Proof.
  intro h.
  inversion h; subst. inversion H2; subst. 
  unfold CIU.
  split; auto.
  split. eapply substitution_tm; eauto using typing_subst_cons, typing_subst_id.
  intros σ Tσ s Ts.
  cbn. 
  eapply nat_step.
  eapply s_prim'.
  eapply s_ifz_succ.
  asimpl.
  done.
Qed.

(*** Examples: Full Eta-equiv *)

Lemma unit_val_eta : 
  forall n Γ v, Γ |-v v ∈ Unit -> log_val n Γ v unit Unit.
Proof.
  intros n Γ v h.
  unfold log_val. split; eauto with rec. 
  split; eauto with rec. 
  intros σ σ' Hs. 
  cbn.
  move: (log_sig_typed1 Hs) => ST1.
  move: (log_sig_typed2 Hs) => ST2.
  split. eauto with rec.
  eauto with rec.
Qed.

Lemma fun_eta : 
  forall n Γ v τ1 τ2,
    Γ |-v v ∈ Arr τ1 τ2 ->
    log_val n Γ (abs (app v⟨↑⟩ (var var_zero))) v (Arr τ1 τ2).
Proof.
  intros.
  unfold log_val.
  repeat split; eauto with renaming rec.
  intros σ σ' Hs.
  move: (substitution_val _ _ _ null σ H (log_sig_typed1 Hs)) => h.
  move: (substitution_val _ _ _ null σ' H (log_sig_typed2 Hs)) => h'.
  destruct v[σ] eqn:EQ.
  destruct f.
  all: inversion h; subst.
  destruct v[σ'] eqn:EQ'.
  destruct f.
  all: inversion h'. subst.
  cbn.
  split. asimpl. auto_unfold in *. rewrite <- substRen_Val.
   rewrite EQ. eauto with renaming rec.
  split. eauto with rec.
  intros w1 w2 Vww.
  move: (V_typed1 Vww) => Tw1.
  move: (V_typed2 Vww) => Tw2.
  have VV: log_val _ Γ v v (Arr τ1 τ2). eapply refl_val; eauto.
  destruct VV as [_ [_ VV]]. 
  specialize (VV _ _ Hs). 
  move: (C_app _ _ _ _ _ _ VV Vww) => h1.
  rewrite EQ in h1. rewrite EQ' in h1. 
  destruct h1 as [_ [_ h1]].
  split. asimpl. rewrite EQ. eauto with renaming rec.
  split. eauto with renaming rec.
  intros s s' STS.
  specialize (h1 s s' STS). clear STS.
  asimpl. 
  rewrite EQ. 
  transitivity (s', app (abs t0) w2); eauto.
  eapply nat_step. eapply StackSmall.s_prim. eapply s_beta.
Qed.

