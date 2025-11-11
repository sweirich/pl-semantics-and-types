(** The rec programming language extended **only**
    with let/cc and exit.

    We use this language to demonstrate CPS conversion, the 
    translation of a language with letcc to a language without 
    letcc.

    The beginning of this file is the same as that in control.control, 
    however, it omits exceptions and delimited continuations and 
    focuses only on letcc.

 *)

(** * Imports *)

(** Type soundness for control operators *)

From Stdlib Require Export ssreflect.
From Stdlib Require Export Program.Equality.
From Stdlib Require Import Logic.FunctionalExtensionality.

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

Fixpoint to_nat (v : Val 0) : option nat := 
  match v with 
  | zero => Some 0
  | succ v1 => match (to_nat v1) with 
                | Some v => Some (S v)
                | None => None
              end
  | _ => None
  end.
 

(** * Primitive reductions 
  
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
  | final_exit v :
    final (nil, exit v)

.

Module Stack.

Inductive step : machine -> machine -> Prop := 
  | s_prim s e e' : 
    e ~>> e' ->
    step (s, e) (s, e')

  | s_pop s e2 v : 
    step (f_let e2 :: s, ret v) (s, e2[v..])

  | s_push s e1 e2 : 
    step (s, let_ e1 e2) (f_let e2 :: s, e1)
  
  (** let/cc *)
  (* letcc *)
  | s_letcc s e : 
      step (s,letcc e) (s, e [(cont s)..])
  (* throw (away the current stacs and switch to the new one) *)
  | s_throw s1 s v :
      step (s1, throw (cont s) v) (s, ret v)

  (** exit *)
  | s_exit s v : 
      step (s , exit v) (nil, exit v)
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

(** * Typing relations *)

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

  (** let/cc *)
  | t_cont s τ  : 
    typing_stack Γ s τ  -> 
    typing_val Γ (cont s) (Cont τ)

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

  (** let/cc *)
  | t_letcc e τ : 
    typing (Cont τ .: Γ) e τ -> 
    typing Γ (letcc e) τ

  | t_throw v1 v2 τ τ' : 
    typing_val Γ v1 (Cont τ') -> 
    typing_val Γ v2 τ' ->
    typing Γ (throw v1 v2) τ

  (** exit *)
  | t_exit v τ τ' : 
    typing_val Γ v τ ->
    typing Γ (exit v) τ'

with typing_frame {n} (Γ : Ctx n) : Frame n -> Ty 0 -> Ty 0 -> Prop := 

  | ft_let e1 τ1 τ2 : 
    typing (τ1 .: Γ) e1 τ2  ->
    typing_frame Γ (f_let e1) τ1 τ2

with typing_stack {n} (Γ : Ctx n) : Stack n -> Ty 0 -> Prop := 
  | st_nil τ : 
    typing_stack Γ nil τ

  | st_cons f s τ τ' : 
    typing_frame Γ f τ τ' ->
    typing_stack Γ s τ' ->
    typing_stack Γ (cons f s) τ 
.

Inductive machine_ok : machine -> Prop := 
  | m_eval s e τ  : 
    typing_stack null s τ  -> 
    typing null e τ ->
    machine_ok (s, e).

(** This version of t_var is easier to work with sometimes
    as it doesn't require the type to already be in the form 
    Γ x. *)
Definition t_var' {n} (Γ : Ctx n) x τ   : Γ x = τ -> typing_val Γ (var x) τ.
intros <-. eapply t_var. Qed.

#[export] Hint Resolve t_var' : rec.

#[export] Hint Constructors typing_val typing 
  typing_frame typing_stack : rec.

(** A tactic to invert typing hypotheses in the context, when the 
    syntax of the value/term/stack/frame is not a variable. *)
Ltac invert_typing := 
  match goal with 
    | [ H : typing_val _ (_ _) _ |- _ ] => inversion H; subst; clear H
    | [ H : typing_stack _ (cons _ _) _  |- _ ] => inversion H; subst; clear H
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
Notation "Γ |-s s ∈ τ" := (typing_stack Γ s τ) (at level 70) : rec_scope.
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
with renaming_stack {n} (Γ : Ctx n) e τ1 {m} (Δ:Ctx m) δ : 
  Γ |-s e ∈ τ1 -> typing_renaming Δ δ Γ -> Δ |-s e⟨δ⟩ ∈ τ1.
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
    all: try solve [eauto with rec renaming].
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
  substitution_stack {n} (Γ : Ctx n) e τ {m} (Δ:Ctx m) σ : 
  Γ |-s e ∈ τ -> typing_subst Δ σ Γ -> Δ |-s e[σ] ∈ τ.
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

Lemma machine_preservation m m' : machine_ok m -> m ↦ m' -> machine_ok m'.
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
  - (* s_letcc *)
    econstructor; eauto with rec.
  - (* s_throw *)
    econstructor; eauto with rec.
  - (* s_exit *)
    econstructor. eauto with rec. instantiate (1 := Void).
    econstructor; eauto.
Qed.

(** * Progress lemma *)

(** A tactic to invert the value typing, when the type is not a
meta-variable. This acts like a canonical forms lemma.
NOTE: we have a separate tactic for Nats because they are the 
only inductively-defined values. We need to be careful about 
how we invert them.

 *)
Ltac canonical_value := 
  lazymatch goal with 
    | [ H : typing_val null _ (Arr _ _) |- _ ] => inversion H; subst; clear H
    | [ H : typing_val null _ (Cont _) |- _ ] => inversion H; subst; clear H
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
  intros h IR. destruct h as [s e τ hs ht].
  (* induction on the typing judgement for the expression e *)
  dependent induction ht.
  all: try is_reducible.
  - (* e is ret v *)
    inversion hs; clear hs; subst. 
    econstructor; eauto.
    inversion H0; subst.
    is_reducible.
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
  - (* throw - can step to saved continuation *)
    canonical_value.
    is_reducible.
Qed.

(* ----------------------------------------------------------- *)
(** * CPS translation *)

Import FinValues.

Reserved Notation "T{ t }". 
Reserved Notation "C{ t }".

Fixpoint transTy {n} (t : Ty n) : Ty n := 
  match t with 
  | Nat => Nat
  | Unit => Unit
  | Void => Void
  | Arr t1 t2 => Arr T{ t1 } (Arr C{ t2} Void)
  | Prod t1 t2 => Prod T{ t1 } T{ t2 }
  | Sum t1 t2 => Sum T{ t1 } T{ t2 }
  | Cont t => C{ t } 
  | var_Ty x => var_Ty x
  | Mu t => Mu T{ t }
  | _ => Void   (* there are extra types in the syntax, but we interpret as Void *)
  end 
where "T{ t }" := (transTy t) 
and "C{ t }" := (Arr (transTy t) Void).



(** The term translation is parameterized by 
    xi - a renaming that describes how variables must be shifted in the output.
    w  - a "continuation value", in the output scope 
 *)

Reserved Notation "E{ e }".
Reserved Notation "V{ v }".
Reserved Notation "S{ s }".

(** Most of the time, we can infer the appropriate renaming argument (xi) 
    automatically. So we define our notation (below) to do so. *)
Ltac infer_xi := 
  first [eassumption | 
         (eapply up_ren); eassumption ].
          

Fixpoint transTm {n} (e : Tm n) {m} (xi : ren n m) (w : Val m) {struct e} : Tm m := 
  match e with 
  | ret v => 
      app w  V{v}
  | let_ e1 e2 => 
      E{e1} (abs (E{e2} w⟨↑⟩))
  | app v1 v2 => 
      let_ (app V{v1} V{v2}) (app (var f0) w⟨↑⟩)
  | ifz v e1 e2 => 
      ifz V{v} (E{e1} w) (E{e2} w⟨↑⟩)
  | prj b v => 
      let_ (prj b V{v}) (app w⟨↑⟩ (var f0))
  | case v e1 e2 => 
      case V{v} (E{e1} w⟨↑⟩) (E{e2} w⟨↑⟩)
  | letcc e => let_ (ret w) (E{e} w⟨↑⟩)
  | throw v1 v2 => app V{v1} V{v2}
  | unfold v => let_ (unfold V{v}) (app  w⟨↑⟩ (var f0))
  | exit v => exit V{v}
  | _ => ret zero
  end
with transVal {n} (v : Val n) {m} (xi : ren n m) {struct v} : Val m  := 
  let fix transStack {n} (s : Stack n) {m} (xi : ren n m) : Val m := 
       match s with 
       | nil => 
           abs (exit (var f0))
       | f_let e2 :: s' => 
           abs (E{ e2 } (transStack s' xi)⟨↑⟩) 
       | _ => zero
       end 
  in
  match v with 
  | var x => (var x)⟨xi⟩
  | unit => unit
  | zero => zero
  | succ v => succ V{v}
  | abs e => abs (ret (abs (transTm e ((up_ren xi) >> shift) (var f0))))
  | prod v1 v2 => prod V{v1} V{v2}
  | inj b v => inj b V{v}
  | fold v => fold V{v}
  | rec v => rec V{v}
  | cont s => transStack s xi
  | _ => zero
  end
where "E{ e }" := (transTm e ltac:(infer_xi)) (only parsing)
and "V{ v }" := (transVal v ltac:(infer_xi)) (only parsing)
.

Notation "E{ e }" := (transTm e _) (only printing).
Notation "V{ v }" := (transVal v _) (only printing).

Reserved Notation "S{ s }".

Fixpoint transStack {n} (s : Stack n) {m} (xi : ren n m) : Val m := 
  match s with 
  | nil => 
      abs (exit (var f0))
  | f_let e2 :: s' => 
      abs (E{ e2 } (ren_Val ↑ S{ s' }))
  | _ => zero
  end
where "S{ s }" := (transStack s ltac:(infer_xi)) (only parsing).

Inductive transCtx : forall {n} (Γ : Ctx n) {m} (Δ : Ctx m), ren n m -> Type := 
  | tc_nil {m} (Δ : Ctx m): 
    transCtx null Δ null
  | tc_abs {n} (Γ : Ctx n) {m} (Δ : Ctx m) τ1 τ2 xi
    : transCtx Γ Δ xi -> 
      transCtx (τ1 .: Γ) (C{τ2} .: ((T{τ1} .: Δ)))
               ((up_ren xi) >> shift)
  | tc_up {n} (Γ : Ctx n) {m} (Δ : Ctx m) τ xi
    : transCtx Γ Δ xi -> 
      transCtx (τ .: Γ) (T{τ} .: Δ) (up_ren xi).

Lemma typing_transCtx  {n} (Γ : Ctx n){m}(Δ : Ctx m) 
  (xi : ren n m) : 
  transCtx Γ Δ xi ->
  forall x, Δ (xi x) = T{ Γ x }.
Proof.
  intro h. induction h.
  - intro x. destruct x.
  - auto_case. 
  - auto_case.
Qed.


(** * The type translation commutes with renaming and substitution *)

Lemma transTy_ren {n} (τ : Ty n) {m} (xi : fin n -> fin m) : 
  ren_Ty xi (T{ τ }) = T{ ren_Ty xi τ }.
Proof.
  move: m xi.
  induction τ.
  all: intros m xi.
  all: auto.
  all: try solve [cbn; rewrite IHτ1; rewrite IHτ2; auto].
  all: try solve [cbn; rewrite IHτ; auto].
Qed.

Lemma transTy_subst {n} (τ : Ty n) {m} (σ : fin n -> Ty m) : 
 subst_Ty (σ >> transTy) (T{τ}) = T{subst_Ty σ τ}.
Proof.
  move: m σ.
  induction τ.
  all: rename n_Ty into n.
  all: intros m σ.
  all: cbn; auto.
  all: try rewrite IHτ1.
  all: try rewrite IHτ2.
  all: try solve [cbn; auto].
  all: try solve [rewrite IHτ; cbn; auto].
    f_equal.
    rewrite <- IHτ.
    f_equal.
    unfold up_Ty_Ty.
    extensionality x.
    destruct x; cbn; try done.
    unfold funcomp.
    rewrite <- transTy_ren.
    done.
Qed.

Lemma transTy_Mu {τ : Ty 1} : 
  (T{τ})[(Mu (T{τ}))..] = T{τ [(Mu τ)..]}.
Proof.
  replace (transTy τ)[((Mu (transTy τ))..)] with 
    (transTy τ)[(((Mu τ)..) >> transTy)].
  unfold subst1, Subst_Ty.
  rewrite transTy_subst; auto.
  eapply ext_Ty. auto_case. 
Qed.


(** * The translation preserves types *)

Fixpoint typing_transTm {n} (Γ : Ctx n) (e : Tm n) τ : 
  Γ |-e e ∈ τ -> forall {m} (Δ : Ctx m) xi w, 
      transCtx Γ Δ xi ->
      Δ |-v w ∈ C{ τ } ->
      Δ |-e E{ e } w ∈ Void
with typing_transVal {n} (Γ : Ctx n) (v : Val n) τ : 
  Γ |-v v ∈ τ -> forall {m} (Δ : Ctx m) xi, 
  transCtx Γ Δ xi ->
  Δ |-v V{v} ∈ T{τ}
with typing_transStack {n} (Γ : Ctx n) (s : Stack n) τ : 
  Γ |-s s ∈ τ -> forall {m} (Δ : Ctx m) xi, 
  transCtx Γ Δ xi ->
  Δ |-v S{s} ∈ C{τ}.
Proof.
-  all: intros h m Δ xi w TG Tw.
   all: inversion h; subst.
   all: cbn.
   + eapply t_app; eauto.
   + eapply typing_transTm; eauto.
     eapply t_abs; eauto.
     eapply typing_transTm; eauto.
     eapply tc_up; eauto.
     eapply renaming_val; eauto.
     eapply typing_renaming_shift.
   + eapply typing_transVal in H; eauto.
     eapply typing_transVal in H0; eauto.
     eapply t_let; eauto.
     cbn in H.
     eapply t_app; eauto.
     eapply t_app; eauto.
     eapply t_var'; eauto.
     cbn. eauto.
     eapply renaming_val; eauto.
     eapply typing_renaming_shift; eauto.
   + eapply typing_transVal in H; eauto.
     eapply typing_transTm in H0; eauto.
     eapply t_ifz; eauto.
     eapply typing_transTm; eauto.
     eapply tc_up; eauto.
     eapply renaming_val; eauto.
     eapply typing_renaming_shift; eauto.
   + eapply typing_transVal in H; eauto. cbn in H.
     eapply t_let; eauto. 
     eapply t_prj1; eauto.
     eapply t_app; eauto.
     eapply renaming_val; eauto with rec.
     eapply typing_renaming_shift; eauto.
     eapply t_var'; eauto.
   + eapply typing_transVal in H; eauto. cbn in H.
     eapply t_let; eauto. 
     eapply t_prj2; eauto.
     eapply t_app; eauto.
     eapply renaming_val; eauto with rec.
     eapply typing_renaming_shift; eauto.
     eapply t_var'; eauto.
   + eapply typing_transVal in H; eauto. cbn in H.
     eapply t_case; eauto.
     eapply typing_transTm; eauto.
     eapply tc_up; eauto.
     eapply renaming_val; eauto with rec.
     eapply typing_renaming_shift; eauto.
     eapply typing_transTm; eauto.
     eapply tc_up; eauto.
     eapply renaming_val; eauto with rec.
     eapply typing_renaming_shift; eauto.
   + (* unfold *)
     eapply typing_transVal in H; eauto. cbn in H.
     eapply t_let; eauto. 
     eapply t_unfold; eauto.
     eapply t_app; eauto.
     eapply renaming_val; eauto with rec.
     eapply typing_renaming_shift; eauto.
     eapply t_var'; eauto.
     rewrite transTy_Mu.
     cbn. done.
   + eapply t_let; eauto with rec.
     eapply typing_transTm; eauto.
     eapply tc_up; eauto.
     eapply renaming_val; eauto with renaming.
   + eapply typing_transVal in H; eauto. cbn in H.
     eapply typing_transVal in H0; eauto. 
     eapply t_app; eauto. 
   + (* exit *)
     eapply typing_transVal in H; eauto.
     eapply t_exit; eauto.     
- intro h; inversion h.
  all: intros m Δ xi TG.
  + eapply t_unit.
  + cbn. eapply typing_transCtx in TG; eauto. 
    eapply t_var'; eauto.
  + eapply t_zero.
  + eapply typing_transVal in H; eauto. cbn in H.
    eapply t_succ; eauto.
  + eapply typing_transVal in H; eauto.
    eapply typing_transVal in H0; eauto. 
    eapply t_prod; eauto.
  + eapply typing_transVal in H; eauto.
    eapply t_inl; eauto.
  + eapply typing_transVal in H; eauto.
    eapply t_inr; eauto.
  + eapply t_abs; eauto.
    eapply t_ret; eauto.
    eapply t_abs; eauto.
    eapply typing_transTm; eauto.
    eapply tc_abs; eauto.
    eapply t_var'. eauto.
  + eapply typing_transVal in H0; eauto. cbn.
    eapply t_rec; eauto.
    destruct τ; eauto.
    eapply tc_up; eauto.
  + eapply typing_transVal in H; eauto.
    cbn.
    eapply t_fold; eauto.
    rewrite transTy_Mu.
    auto.
  + eapply typing_transStack in H; eauto.
- intros h; inversion h.
  all: intros m Δ xi TG.
  all: cbn.
  + 
    eapply t_abs; eauto.
    eapply t_exit; eauto.
    eapply t_var'; eauto. 
  + inversion H; subst.
    eapply t_abs; eauto.
    eapply typing_transTm; eauto with renaming.
    eapply tc_up; eauto.
    eapply renaming_val; eauto with renaming.    
Qed.

(** * top-level result *)

Corollary top_level : 
  forall e tau, 
    null |-e e ∈ tau -> 
    null |-v abs (transTm e null (var f0)) ∈ Arr C{tau} Void.
Proof.          
  intros e tau h.
  eapply typing_transTm with (Δ := C{tau} .: null)(w := var f0) in h.
  eapply t_abs; eauto.
  eapply tc_nil; eauto.
  eapply t_var'; eauto.
Qed.

(* ----------------------------------------------------- *)

