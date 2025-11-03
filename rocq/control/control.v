(** The rec programming language extended with various control operations: exceptions, let/cc 
    and effect handlers *)

(** * Imports *)

(** Type soundness for control operators *)

From Stdlib Require Export ssreflect.
From Stdlib Require Export Program.Equality.
Require Export common.core.
Require Export common.fintype.

Require Export common.fin_util.
Require Export common.relations.
Require Export common.renaming.

(** The syntax file defines notations for printing. However, this syntax can 
    sometimes be confusing so we disable it here. *)
Require Export control.syntax.
Disable Notation "↑__Val" (all).
Disable Notation "↑__Tm" (all).
Disable Notation "'__Val'" (all).
Require Export control.typesyntax.
Disable Notation "↑__Ty" (all).
Disable Notation "'__Ty'" (all).

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
  | s_app_rec : forall (v : Val 1) (v1 : Val 0), 
      app (rec v) v1 ~>> app v[(rec v)..] v1
  | s_prj_rec : forall (b : bool) (v : Val 1), 
      prj b (rec v) ~>> prj b v[(rec v)..]
  | s_unfold : forall v : Val 0, 
      unfold (fold v) ~>> ret v 
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
    final (nil, raise v)
  | final_eff v : 
    final (nil, perform v)
.

Module Stack.

(** Exceptions: Search for a 'try' frame on the stack for a raised exception *)
Fixpoint find_exn (s : stack) (v : Val 0) : machine := 
  match s with 
  (* we found a try block *)
  | cons (f_try e2) k => (k, e2[v..])
  (* no handler, keep looking *)
  | cons _ k  => find_exn k v
  (* uncaught exception *)
  | nil => (nil, raise v) 
  end.

(** Effect Handlers: Search for an effect handler for the effect `eff n`.

   As we search the stack, we need to record all of the frames that we
   encounter along the way, using the accumulating parameter `seen`. 
   We use these frames to create the resumption continuation passed 
   to the effect handler. *)

Fixpoint find_eff (s : stack) (n : nat) (seen : list (Frame 0)) : machine :=
    match s with 
    | cons (f_handle e2 n' e2') k => 
        (* check to see if we've found the handler for *this* effect *)
        if PeanoNat.Nat.eqb n n' then
          (* we keep the current handler as part of the continuation value, 
             but do not save the entire stack. This is a "deep" handler. *)
          let d := List.rev seen ++ (f_handle e2 n e2' :: nil) in
          (k,  e2'[(cont d)..])
        else
          (* keep looking *)
          find_eff k n (f_handle e2 n' e2' :: seen)
    | cons f k  => 
        (* keep looking *)
        find_eff k n (f :: seen)
    | nil => 
        (* uncaught effect *)
        (nil, perform (eff n)) 
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
  | s_raise f s v : 
    step (f :: s, raise v) (find_exn (cons f s) v) 

  (* install (push) an exception handler *)
  | s_try s e1 e2 : 
    step (s, try e1 e2) (f_try e2 :: s, e1)
  (* discard (pop) an exception hander *)
  | s_discard_try s e2 v : 
    step (f_try e2 :: s, ret v) (s,ret v)
  
  (** let/cc *)
  (* letcc *)
  | s_letcc s e : 
      step (s,letcc e) (s, e [(cont s)..])
  (* throw (away the current stacs and switch to the new one) *)
  | s_throw s1 s v :
      step (s1, throw (cont s) v) (s, ret v)

  (** effect handlers *)
  (* perform an effect *)
  | s_perform f s n : 
      step (cons f s, perform (eff n))
        (find_eff (cons f s) n nil)

  (* install (push) an effect handler *)
  | s_handle s e1 n e2 e2' : 
    step (s, handle e1 e2 n e2') (f_handle e2 n e2' :: s, e1)
  (* discard (pop) an effect hander *)
  | s_handle_ret s e2 n e2' v : 
    step (f_handle e2 n e2' :: s, ret v) (s, e2[v..])
  (* invoke a saved continuation without discarding the current 
     stack *)
  | s_continue s1 s2 v :
    step (s1, continue (cont s2) v) (s2 ++ s1, ret v)

  
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

Definition allows_rec_ty (ty : Ty 0) := 
  match ty with 
  | Arr _ _ => true
  | Prod _ _ => true
  | _ => false
  end.

(** Declared types of effect handlers *)
Parameter Phi : nat -> Ty 0.

Definition Ctx (n : nat) := fin n -> Ty 0.

Inductive typing_val  {n} (Γ : Ctx n) : Val n -> Ty 0 -> Prop := 
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

  | t_abs e τ1 τ2 : 
    typing (τ1 .: Γ) e τ2 -> 
    typing_val Γ (abs e) (Arr τ1 τ2)

  | t_rec v τ : 
    allows_rec_ty τ = true ->
    typing_val (τ .: Γ) v τ -> 
    typing_val Γ (rec v) τ

  | t_fold v τ : 
    typing_val Γ v (τ [(Mu τ) ..]) ->
    typing_val Γ (fold v) (Mu τ)

  | t_exn k : 
    typing_val Γ (exn k) Exn

  (** let/cc *)
  | t_cont s τ τ2 : 
    typing_stack Γ s τ τ2 -> 
    typing_val Γ (cont s) (Cont τ)

  (** effect handlers *)
  | t_decont s τ τ2 : 
    typing_stack Γ s τ τ2 -> 
    typing_val Γ (cont s) (DeCont τ τ2)

  | t_eff n τ : 
    Phi n = τ -> 
    typing_val Γ (eff n) (Eff τ)


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

  | t_prj1 v τ1 τ2 :
    typing_val Γ v (Prod τ1 τ2) -> 
    typing Γ (prj1 v) τ1

  | t_prj2 v τ1 τ2 :
    typing_val Γ v (Prod τ1 τ2) -> 
    typing Γ (prj2 v) τ2

  | t_case v e1 e2 τ1 τ2 τ : 
    typing_val Γ v (Sum τ1 τ2) ->
    typing (τ1 .: Γ) e1 τ ->
    typing (τ2 .: Γ) e2 τ ->
    typing Γ (case v e1 e2) τ

  | t_unfold v τ : 
    typing_val Γ v (Mu τ) ->
    typing Γ (unfold v) (τ [(Mu τ) ..]) 

  (** exceptions *)
  | t_raise v τ : 
    typing_val Γ v Exn -> 
    typing Γ (raise v) τ

  | t_try e1 e2 τ : 
    typing Γ e1 τ ->
    typing (Exn .: Γ) e2 τ ->
    typing Γ (try e1 e2) τ

  (** let/cc *)
  | t_letcc e τ : 
    typing (Cont τ .: Γ) e τ -> 
    typing Γ (letcc e) τ

  | t_throw v1 v2 τ τ' : 
    typing_val Γ v1 (Cont τ') -> 
    typing_val Γ v2 τ' ->
    typing Γ (throw v1 v2) τ

  (** effect handlers *)
  | t_perform v τ : 
    typing_val Γ v (Eff τ) ->
    typing Γ (perform v) τ

  | t_handle e1 e2 n e2' τ1 τ2 τ : 
    typing Γ e1 τ1 ->
    typing (τ1 .: Γ) e2 τ ->
    Phi n = τ2 ->
    typing (DeCont τ2 τ .: Γ) e2' τ ->
    typing Γ (handle e1 e2 n e2') τ

  | t_continue v1 v2 τ1 τ: 
    typing_val Γ v1 (DeCont τ1 τ) ->
    typing_val Γ v2 τ1 ->
    typing Γ (continue v1 v2) τ


with typing_frame {n} (Γ : Ctx n) : Frame n -> Ty 0 -> Ty 0 -> Prop := 

  | ft_let e1 τ1 τ2 : 
    typing (τ1 .: Γ) e1 τ2  ->
    typing_frame Γ (f_let e1) τ1 τ2

  (** exceptions *)
  | ft_try e2 τ :
    typing (Exn .: Γ) e2 τ -> 
    typing_frame Γ (f_try e2) τ τ

  (** effect handlers *)
  | ft_handle e2 m e2' τ1 τ2 τ : 
    typing (τ1 .: Γ) e2 τ ->
    Phi m = τ2 ->
    typing (DeCont τ2 τ .: Γ) e2' τ -> 
    typing_frame Γ (f_handle e2 m e2') τ1 τ
    

with typing_stack {n} (Γ : Ctx n) : Stack n -> Ty 0 -> Ty 0 -> Prop := 
  | st_nil τ : 
    typing_stack Γ nil τ τ

  | st_cons f s τ τ' τ2 : 
    typing_frame Γ f τ τ' ->
    typing_stack Γ s τ' τ2 ->
    typing_stack Γ (cons f s) τ τ2
.

Inductive machine_ok : machine -> Prop := 
  | m_eval s e τ τ' : 
    typing_stack null s τ τ' -> 
    typing null e τ ->
    machine_ok (s, e).

(** This version of t_var is easier to work with sometimes
    as it doesn't require the type to already be in the form 
    Γ x. *)
Definition t_var' {n} (Γ : Ctx n) x τ   : Γ x = τ -> typing_val Γ (var x) τ.
intros <-. eapply t_var. Qed.

Definition st_cons'  {n} (Γ : Ctx n) f s τ τ' τ2 s' : 
    typing_frame Γ f τ τ' ->
    typing_stack Γ s' τ' τ2 ->
    s = cons f s' ->
    typing_stack Γ s τ τ2.
intros ? ? ->. eapply st_cons; eauto.
Qed.

#[export] Hint Resolve t_var' st_cons' : rec.

#[export] Hint Constructors typing_val typing 
  typing_frame typing_stack : rec.

(** A tactic to invert typing hypotheses in the context, when the 
    syntax of the value/term/stack/frame is not a variable. *)
Ltac invert_typing := 
  match goal with 
    | [ H : typing_val _ (_ _) _ |- _ ] => inversion H; subst; clear H
    | [ H : typing_stack _ (cons _ _) _ _ |- _ ] => inversion H; subst; clear H
    | [ H : typing _ (_ _) _ |- _ ] => inversion H; subst; clear H
    | [ H : typing_frame _ (_ _) _ _ |- _ ] => inversion H; subst; clear H
    end.


(** * Notation *)

Module Notations.
Infix "↦"  := Stack.step (at level 70) : rec_scope.
Infix "↦*"  := (multi Stack.step) (at level 70) : rec_scope.
Notation "Γ |-v v ∈ τ" := (typing_val Γ v τ) (at level 70) : rec_scope.
Notation "Γ |-e e ∈ τ" := (typing Γ e τ) (at level 70) : rec_scope.
Notation "Γ |-f f ∈ τ1 ~> τ2" := (typing_frame Γ f τ1 τ2) (at level 70): rec_scope.
Notation "Γ |-s s ∈ τ1 ~> τ2" := (typing_stack Γ s τ1 τ2) (at level 70) : rec_scope.
End Notations.

Import Notations.

(** * Basic properties of the typing relation *)


(** Renaming and substitution for stacks. Note: autosubst doesn't generate
    these instances for us. *)
#[global]
Instance Subst_Stack  {m n : nat}: (Subst1 _ _ _) :=
  fun (sigma : fin m -> Val n) => list_map (subst_Frame sigma).
#[global]
Instance Ren_Stack  {m n : nat}: (Ren1 _ _ _) :=
  fun (xi : fin m -> fin n) => list_map (ren_Frame xi).


(** Renaming lemma *)

Fixpoint renaming_val {n} (Γ : Ctx n) v τ {m} (Δ:Ctx m) δ : 
  Γ |-v v ∈ τ -> typing_renaming Δ δ Γ -> Δ |-v v⟨δ⟩ ∈ τ
with renaming_tm {n} (Γ : Ctx n) e τ {m} (Δ:Ctx m) δ : 
  Γ |-e e ∈ τ -> typing_renaming Δ δ Γ -> Δ |-e e⟨δ⟩ ∈ τ
with renaming_frame {n} (Γ : Ctx n) e τ1 τ2 {m} (Δ:Ctx m) δ : 
  Γ |-f e ∈ τ1 ~> τ2 -> typing_renaming Δ δ Γ -> Δ |-f e⟨δ⟩ ∈ τ1 ~> τ2
with renaming_stack {n} (Γ : Ctx n) e τ1 τ2 {m} (Δ:Ctx m) δ : 
  Γ |-s e ∈ τ1 ~> τ2 -> typing_renaming Δ δ Γ -> Δ |-s e⟨δ⟩ ∈ τ1 ~> τ2.
Proof. 
  - intros h tR; inversion h.
    all: asimpl.
    all: try solve [econstructor; eauto with renaming].
    + (* var case *)
      eapply t_var'; eauto. 
  - intros h tR; inversion h.
    all: asimpl.
    all: try solve [econstructor; eauto with renaming].
  - intros h tR; inversion h.
    all: asimpl.
    all: try solve [econstructor; eauto with renaming].
  - intros h tR; inversion h; subst.
    all: try destruct k; cbn.
    all: try solve [eauto using st_cons' with rec renaming].
Qed.

Hint Resolve renaming_val renaming_tm renaming_frame renaming_stack : rec.

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
  substitution_tm {n} (Γ : Ctx n) e τ {m} (Δ:Ctx m) σ : 
  Γ |-e e ∈ τ -> typing_subst Δ σ Γ -> Δ |-e e[σ] ∈ τ
with 
  substitution_frame {n} (Γ : Ctx n) e τ τ' {m} (Δ:Ctx m) σ : 
  Γ |-f e ∈ τ ~> τ' -> typing_subst Δ σ Γ -> Δ |-f e[σ] ∈ τ ~> τ'
with 
  substitution_stack {n} (Γ : Ctx n) e τ τ' {m} (Δ:Ctx m) σ : 
  Γ |-s e ∈ τ ~> τ' -> typing_subst Δ σ Γ -> Δ |-s e[σ] ∈ τ ~> τ'.
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

(* Property about list reverse *)
Lemma rev_snoc {A} (f : A) (l : list A) : 
  List.rev (f :: l) = (List.rev l) ++ (f :: nil).
Proof.
  induction l; eauto.
Qed.

(** The append operation on stacks preserves types *)
Lemma st_app {n} (Γ : Ctx n) k1 k2 τ1 τ2 τ3 : 
  typing_stack Γ k1 τ1 τ2 ->
  typing_stack Γ k2 τ2 τ3 ->
  typing_stack Γ (k1 ++ k2) τ1 τ3.
Proof.       
  move=> h1.
  move: k2 τ3.
  dependent induction h1; intros.
  - cbn; eauto.
  - repeat invert_typing. cbn.
    eapply st_cons'; eauto.
Qed.

(** The [find_exn] operation produces a well-formed next state *)
Lemma preservation_find_exn v : 
  typing_val null v Exn ->
  forall l τ τ', typing_stack null l τ τ' -> 
                machine_ok (Stack.find_exn l v).
Proof.
  intro hv.
  induction l; intros τ τ' h.
  - econstructor; eauto with rec.
  - inversion h. subst.
    inversion H1; cbn; subst; eauto.
    econstructor; eauto with rec.
    eapply substitution_tm; eauto with rec.
Qed.

Lemma preservation_find_eff n τ0 :
  Phi n = τ0 -> 
  forall s τ1 τ',  typing_stack null s τ1 τ' -> 
              forall s1, 
                typing_stack null (List.rev s1) τ0 τ1 -> 
                machine_ok (Stack.find_eff s n s1).
Proof.
  intros SEQ l τ1 τ' hl.
  dependent induction hl; intros l1 hl1; cbn.
  + eapply m_eval. 
    instantiate (1 := Phi n).
    econstructor; eauto with rec.
    econstructor; eauto with rec.
  + inversion H; subst; cbn.
    * (* top of stack is f_let. *)
      eapply IHhl; auto.
      rewrite rev_snoc.
      eapply st_app; eauto with rec.
    * (* top is f_try *)
      eapply IHhl; auto.
      rewrite rev_snoc.
      eapply st_app; eauto with rec.
    * (* top is f_handle *)
      destruct (PeanoNat.Nat.eqb n m) eqn:hEQ.
      - rewrite  PeanoNat.Nat.eqb_eq in hEQ. subst.
        eapply m_eval; eauto.
        eapply substitution_tm; eauto.
        eapply typing_subst_cons; eauto with rec.
        eapply t_decont.
        eapply st_app; eauto with rec.
      - eapply IHhl; auto.
        rewrite rev_snoc.
        eapply st_app; eauto with rec.
Qed.

Lemma machine_preservation m m' : machine_ok m -> Stack.step m m' -> machine_ok m'.
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
  - (* s_raise *)
    eapply preservation_find_exn; eauto with rec.
  - (* s_try *)
    econstructor; eauto with rec.
  - (* s_discard_try *)
    econstructor; eauto with rec.
  - (* s_letcc *)
    econstructor; eauto with rec.
  - (* s_throw *)
    econstructor; eauto with rec.
  - (* s_perform *)
    eapply preservation_find_eff; cbn; eauto with rec.
  - (* s_handle *)
    econstructor; eauto with rec.
  - (* s_handle_ret *)
    econstructor; eauto with rec.
  - (* s_continue *)
    econstructor; eauto using st_app with rec.
  
Qed.

(** progress *)

(** A tactic to invert the value typing, when the type is not a
meta-variable. This acts like a canonical forms lemma.
NOTE: we have a separate tactic for Nats because they are the 
only inductively-defined values. We need to be careful about 
how we invert them.

 *)
Ltac canonical_value := 
  lazymatch goal with 
    | [ H : typing_val null _ (Arr _ _) |- _ ] => inversion H; subst; clear H
    | [ H : typing_val null _ Exn |- _ ] => inversion H; subst; clear H
    | [ H : typing_val null _ (Cont _) |- _ ] => inversion H; subst; clear H
    | [ H : typing_val null _ (Eff _) |- _ ] => inversion H; subst; clear H
    | [ H : typing_val null _ (DeCont _ _) |- _ ] => inversion H; subst; clear H
    | [ H : typing_val null _ (List _) |- _ ] => inversion H; subst; clear H
    | [ H : typing_val null _ (Prod _ _) |- _ ] => inversion H; subst; clear H
    | [ H : typing_val null _ (Sum _ _) |- _ ] => inversion H; subst; clear H
    | [ H : typing_val null _ (Mu _) |- _ ] => inversion H; subst; clear H
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
Lemma machine_progress m : machine_ok m -> Stack.irreducible m -> final m.
Proof.
  intros h IR. destruct h as [s e τ τ' hs ht].
  (* induction on the typing judgement for the expression e *)
  dependent induction ht.
  all: try is_reducible.
  - (* e is ret v *)
    inversion hs; clear hs; subst. econstructor; eauto. 
    destruct f; is_reducible.
  - (* e is app v1 v2 *)
    canonical_value.
    is_reducible. (* beta reduction *)
    is_reducible. (* rec reduction *)
  - (* ifz *)
    canonical_Nat.
    is_reducible. (* zero case *)
    is_reducible. (* successor *)
  - (* prj1 *)
    canonical_value.
    is_reducible. 
    is_reducible. 
  - (* prj2 *)
    canonical_value. is_reducible. is_reducible. 
  - (* case *) 
    canonical_value.
    is_reducible. is_reducible. 
  - (* unfold *) 
    canonical_value. is_reducible. 
  - (* raise v *) 
    inversion hs; clear hs; subst.
    econstructor; eauto with rec.  (* uncaught exn is final *)
    is_reducible.
  - (* throw - can step to saved continuation *)
    canonical_value.
    is_reducible.
  - (* perform *)
    canonical_value.
    inversion hs; subst; clear hs. econstructor. (* uncaught perform is final *)
    is_reducible. 
  - (* continue *)
    canonical_value.
    is_reducible.

Qed.


