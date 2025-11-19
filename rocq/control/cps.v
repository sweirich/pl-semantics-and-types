From Stdlib Require Import FunctionalExtensionality.
From Stdlib Require Import Arith Psatz.

Require Export control.letcc.

Open Scope rec_scope.
Import letcc.Notations.

(* ----------------------------------------------------------- *)
(** * CPS translation *)

(** * This translation uses continuation-passing style to convert
      the letcc language to a simpler one that does not include 
      letcc or throw expressions, and has no need of an explicit 
      stack in the semantics.

      The simpler language is basically [rec] augmented with an
      [exit] term. We need the [exit] term to translate explicit
      continuation values. Without [letcc], we don't need to have
      [exit], and our CPS conversion can be generic about 
      the answer type.
 *)

Import FinValues.

Reserved Notation "T{ t }".   (* Type translation *)
Reserved Notation "C{ t }".   (* "Continuation" type: T{t} -> Void *)

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

(** The term/value and stack translations are parameterized by 
    ξ - a renaming that describes how variables must be shifted in the output. 

    Pottier shifts the terms during the translation before the recursive calls. 
    As a result, his translation is not structurally recursive. We defer this 
    renaming, accumulating it in ξ, before finally applying it in the variable
    case of the translation. But there is no free lunch: we have to pay for this
    "simpler" translation with more work later.
 *)

Reserved Notation "E{ e } ξ" (at level 8).
Reserved Notation "V{ v } ξ" (at level 8).
Reserved Notation "S{ s } ξ" (at level 8).

(* Whenever we enter a new scope, we need to modify the renaming. *) 
(* This notation is analogus to ⇑σ *)
Notation "ξ ⤉" := (up_ren ξ) (at level 6).  (* uparrowbarred *)

(* For the term translation, the parameter w is a "continuation value", 
   and uses variables from the output scope  *)
Fixpoint transTm {n} (e : Tm n) {m} (ξ : ren n m) (w : Val m) {struct e} : Tm m := 
  match e with 
  | ret v => 
      app w  V{v}ξ
  | let_ e1 e2 => 
      E{e1}ξ (abs (E{e2}ξ⤉ w⟨↑⟩))
  | app v1 v2 => 
      let_ (app V{v1}ξ V{v2}ξ) (app (var f0) w⟨↑⟩)
  | ifz v e1 e2 => 
      ifz (V{v} ξ) (E{e1}ξ w) (E{e2}ξ⤉ w⟨↑⟩)
  | prj b v => 
      let_ (prj b V{v}ξ) (app w⟨↑⟩ (var f0))
  | case v e1 e2 => 
      case V{v}ξ (E{e1}ξ⤉ w⟨↑⟩) (E{e2}ξ⤉ w⟨↑⟩)
  | letcc e => let_ (ret w) (E{e}ξ⤉ w⟨↑⟩)
  | throw v1 v2 => app V{v1}ξ V{v2}ξ
  | unfold v => let_ (unfold V{v}ξ) (app  w⟨↑⟩ (var f0))
  | exit v => exit V{v}ξ
  | _ => ret zero  (* extra terms/stacks/values go to zero *)
  end
with transVal {n} (v : Val n) {m} (ξ : ren n m) {struct v} : Val m  := 
  (* To satisfy the termination checker, we need to define the 
     stack translation locally to the value translation. 
     But, we cannot use our notation for the stack translation yet.
   *)
  let fix transStack {n} (s : Stack n) {m} (ξ : ren n m) : Val m := 
  match s with 
  | nil => 
      abs (exit (var f0)) 
  | f_let e2 :: s' => 
      abs (E{ e2 }ξ⤉ (transStack s' ξ)⟨↑⟩) 
  | _ => zero
  end 
  in
  match v with 
  | var x => (var x)⟨ξ⟩
  | unit => unit
  | zero => zero
  | succ v => succ V{v}ξ
  | abs e => abs (ret (abs (E{e}(ξ⤉ >> ↑)(var f0))))
  | prod v1 v2 => prod V{v1}ξ V{v2}ξ
  | inj b v => inj b V{v}ξ
  | fold v => fold V{v}ξ
  | rec v => rec V{v}ξ⤉
  | cont s => transStack s ξ
  | _ => zero
  end
where "E{ e } ξ" := (transTm e ξ) (only parsing)
and "V{ v } ξ" := (transVal v ξ) (only parsing).

(* Repeat the definition of the stack translation at top level *)
Fixpoint transStack {n} (s : Stack n) {m} (ξ : ren n m) : Val m := 
  match s with 
  | nil => 
      abs (exit (var f0))
  | f_let e2 :: s' => 
      abs (E{e2}ξ⤉ (S{s'}ξ)⟨↑⟩) 
  | _ => zero
  end
where "S{ s } ξ" := (transStack s ξ).




(* ----------------------------------------------------------- *)
(** * The type translation commutes with renaming and substitution *)

Lemma transTy_ren {n} (τ : Ty n) {m} (ξ : fin n -> fin m) : 
  ren_Ty ξ (T{ τ }) = T{ ren_Ty ξ τ }.
Proof.
  move: m ξ.
  induction τ.
  all: intros m ξ.
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

(* ----------------------------------------------------------- *)
(** * Typing context translation *)

Definition ξ0 : fin 0 -> fin 0 := id.
Definition ξ1 : fin 0 -> fin 1 := ξ0 >> ↑.

Fixpoint base n : ren 0 n := 
  match n with 
  | 0 => ξ0
  | S m => base m >> ↑
  end.

(** * Define the translation of typing contexts relationally *)
(** The input and output contexts are in two different scopes.
    Furthermore, the typing context doesn't know how variables 
    were bound (via function argument or other). So we have to 
    allow the possibility of a following continuation argument
    at any point.
  *)
Inductive transCtx : forall {n} (Γ : Ctx n) {m} (Δ : Ctx m), ren n m -> Type := 
  | tc_nil {m} (Δ : Ctx m): 
    transCtx null Δ (base m)
  | tc_abs {n} (Γ : Ctx n) {m} (Δ : Ctx m) τ1 τ2 ξ
    : transCtx Γ Δ ξ -> 
      transCtx (τ1 .: Γ) (C{τ2} .: ((T{τ1} .: Δ)))
               ((up_ren ξ) >> shift)
  | tc_up {n} (Γ : Ctx n) {m} (Δ : Ctx m) τ ξ
    : transCtx Γ Δ ξ -> 
      transCtx (τ .: Γ) (T{τ} .: Δ) (up_ren ξ).

Lemma typing_transCtx  {n} (Γ : Ctx n){m}(Δ : Ctx m) 
  (ξ : ren n m) : 
  transCtx Γ Δ ξ ->
  forall x, Δ (ξ x) = T{ Γ x }.
Proof.
  intro h. induction h.
  - intro x. destruct x.
  - destruct x; cbn; eauto. 
  - destruct x; cbn; eauto.
Qed.

(* ----------------------------------------------------------- *)
(** * The translation preserves types *)

Fixpoint typing_transTm {n} (Γ : Ctx n) (e : Tm n) τ : 
  Γ |-e e ∈ τ -> forall {m} (Δ : Ctx m) ξ w, 
      transCtx Γ Δ ξ ->
      Δ |-v w ∈ C{ τ } ->
      Δ |-e E{ e }ξ w ∈ Void
with typing_transVal {n} (Γ : Ctx n) (v : Val n) τ : 
  Γ |-v v ∈ τ -> forall {m} (Δ : Ctx m) ξ, 
  transCtx Γ Δ ξ ->
  Δ |-v V{v}ξ ∈ T{τ}
with typing_transStack {n} (Γ : Ctx n) (s : Stack n) τ : 
  Γ |-s s ∈ τ -> forall {m} (Δ : Ctx m) ξ, 
  transCtx Γ Δ ξ ->
  Δ |-v S{s}ξ ∈ C{τ}.
Proof. (* FILL IN HERE *) Admitted.

(** * top-level result for type translation *)

Corollary top_level1 : 
  forall e tau, 
    null |-e e ∈ tau -> 
    null |-v abs (transTm e ξ1 (var f0)) ∈ Arr C{tau} Void.
Proof.          
  intros e tau h.
  eapply typing_transTm with (Δ := C{tau} .: null)(w := var f0)(ξ:=ξ1) in h.
  eapply t_abs; eauto. 
  eapply @tc_nil with (m := 1); eauto.
  eapply t_var'; eauto.
Qed.

Corollary top_level2 : 
  forall e tau, 
    null |-e e ∈ tau -> 
    null |-e transTm e ξ0 (abs (exit (var f0))) ∈ Void.
Proof.          
  intros e tau h.
  eapply typing_transTm; eauto.
  eapply @tc_nil with (m := 0).
  eapply t_abs; eauto.
  eapply t_exit; eauto.
  eapply t_var'; eauto.
Qed.


(* ----------------------------------------------------- *)
(** Semantic simulation *)

(* The rest of this file shows semantic simulation, that

    <s1,e1> |-> <s2,e2> implies that E{e1} S{s1} ~>* E{e2} S{s2}

   using the small step semantics shown below.

   This small-step semantics does not know how to evaluate [letcc] or [throw]
   because it does not have an explicit stack. But that is fine because CPS
   conversion will remove those terms from the output. Instead, this judgement
   is the usual small-step semantics of [rec], plus an additional rule
   [s_let_exist] implementing the [exit v] operation.  *)
Module Small.

Inductive step : Tm 0 -> Tm 0 -> Prop := 
  | s_prim e e' : 
    e ~>> e' ->
    step e e'
  | s_let e1 e1' e2 :
    step e1 e1' -> 
    step (let_ e1 e2) (let_ e1' e2)
  | s_let_ret v e2 : 
    step (let_ (ret v) e2) (e2 [v..])
  | s_let_exit v e2 : 
    step (let_ (exit v) e2) (exit v).
  
End Small.

(* Beyond this point things get *much* more difficult. You can tell this
   because the next step is to define a size function for terms/values/stack
   and show that size is stable under renaming. *)

Fixpoint size_Val {n : nat} (v: Val n) : nat :=
  let fix size_Stack {n} (s : list (Frame n)) := 
    match s with 
    | f_let e1 :: s' => S (size_Tm e1 + size_Stack s')
    | _ => 0
    end in
  match v with 
  | var n => 1 
  | unit => 1
  | zero => 1
  | succ v => S (size_Val v)
  | prod v1 v2 => S (size_Val v1 + size_Val v2)
  | inj _ v => S (size_Val v)
  | abs e => S (size_Tm e)
  | rec v => S (size_Val v)
  | fold v => S (size_Val v)
  | cont vs => S (size_Stack vs)
  | _ => 0
  end
with 
size_Tm {n : nat} (e : Tm n) : nat :=
  match e with 
  | ret v => S (size_Val v)
  | let_ e1 e2 => S (size_Tm e1 + size_Tm e2)
  | ifz v e1 e2 => S (size_Val v + size_Tm e1 + size_Tm e2)
  | prj b v => S (size_Val v)
  | case v e1 e2 => S (size_Val v + size_Tm e1 + size_Tm e2)
  | app v1 v2 => S (size_Val v1 + size_Val v2)
  | unfold v => S (size_Val v)
  | letcc e => S (size_Tm e)
  | exit v => S (size_Val v)
  | throw v1 v2 => S (size_Val v1 + size_Val v2)
  | _ => 0
  end.
Fixpoint size_Stack {n} (s: list (Frame n)) : nat := 
  match s with 
  | f_let e1 :: s' => S (size_Tm e1 + size_Stack s')
  | _ => 0
  end.

(** * Renaming doesn't change the size of a term *)
Fixpoint size_ren_Val {n:nat} {v : Val n}{m} {ξ : ren n m} :
  size_Val (v⟨ξ⟩) = size_Val v
with size_ren_Tm {n:nat} {e : Tm n}{m} {ξ : ren n m} :
  size_Tm (e⟨ξ⟩) = size_Tm e.
Proof.
  - destruct v.
    all: cbn. 
    all: try rewrite size_ren_Val.
    all: try rewrite size_ren_Tm.
    all: eauto.
    induction l. cbn. auto.
    cbn. destruct a; cbn. auto. f_equal.
    inversion IHl.
    rewrite size_ren_Tm. f_equal.  auto.
  - destruct e.
    all: cbn. 
    all: try rewrite size_ren_Val.
    all: try rewrite size_ren_Tm.
    all: eauto.
Qed.

(* ------------------------------------------------------ *)

(** * Autosubst helpers *)

(* The autosubst type classes make reasoning equational 
   reasoning painful --- the rewriting tactics don't work up 
   to definitional equality: whether the Gallina term 
   is "subst_Tm σ e" or "Subst_Tm σ e" or "subst1 σ e" 
   matters. For more flexibility, we define rewriting 
   tactics that unfold class instances first: both in 
   the rewriting lemma and in the goal. *)
Ltac unfold_rewrite f := 
   let rw := fresh in
   pose proof f as rw;
   cbn in rw;
   auto_unfold in *; rewrite -> rw; clear rw.

Ltac unfold_erewrite f := 
   let rw := fresh in
   pose proof f as rw;
   cbn in rw;
   auto_unfold in *; erewrite -> rw; clear rw.

(* The [asimpl] tactic is often *slow*. These lemmas provide
   more targetted rewrites to speed up the interactive development. *)

Lemma substFresh (v1 v2 : Val 0) :
  v1⟨↑⟩[ v2 .: var ] = v1.
Proof.
  asimpl. done.
Qed.

Lemma substFresh' {n m} {w : Val n}{ σ : fin n -> Val m } : 
  w⟨↑⟩[⇑ σ] =  w[σ]⟨↑⟩.
Proof. 
  asimpl. done.
Qed.


Lemma ren_commute {m n}{ e : Tm (S n)}{ξ : fin n -> fin m} :
  e ⟨id ⤉⟩⟨ξ⤉⟩ = e⟨ξ⤉⟩⟨id ⤉⟩.
Proof.
  asimpl. done.
Qed.
Lemma subst_commute {m n}{ e2 : Tm (S n)}{σ : fin n -> Val m} :
  e2 ⟨id ⤉⟩[⇑ σ] = e2[⇑ σ]⟨id ⤉⟩.
Proof.
  asimpl. done.
Qed.

Lemma up_ren_ren_ext k l m (xi: ren k l) (zeta: ren l m) :
 (xi ⤉ >> zeta ⤉) = (xi >> zeta) ⤉.
Proof.
  extensionality x. erewrite <- up_ren_ren; eauto.
Qed.


(** * Renaming composition *) 
(* This lemma gives us flexibility with the renaming argument
   of the translation. We can apply it to the term, or compose
  it with the renaming argument: either way works. *)
Lemma transTm_ren_comp {n} (e : Tm n) {m} (xi : fin n -> fin m) 
   {p} (rho : fin m -> fin p) (k : Val p) : 
  transTm (e⟨xi⟩) rho k = transTm e (xi >> rho) k
with transVal_ren_comp {n} (v : Val n) {m} (xi : fin n -> fin m) 
  {p} (rho : fin m -> fin p)  : 
  transVal (v⟨xi⟩) rho = transVal v (xi >> rho).
Proof. (* FILL IN HERE *) Admitted.

(** This special case of the above lemma means that we can 
    always make the renaming argument [id] in the translation. 
    This is important for being able to state the substitution proofs. 
*)
Lemma transTm_ren_comp' {n} (e : Tm n) {m} (xi : fin n -> fin m) 
   (k : Val m) : 
  transTm e xi k = transTm (e⟨xi⟩) id k.
rewrite transTm_ren_comp. asimpl. done.
Qed.
Lemma transVal_ren_comp' {n} (v : Val n) {m} (xi : fin n -> fin m) : 
  transVal v xi = transVal (v⟨xi⟩) id.
Proof.
  rewrite transVal_ren_comp. asimpl. done.
Qed.


(** * Renaming commutes with the term/value/stack translation. *)


 Lemma transTm_ren {n} (e : Tm n) {m} (xi : fin n -> fin m) 
  (k : Val m) {p} (rho : fin m -> fin p)  : 
  (transTm e xi k)⟨rho⟩ = transTm e (xi >> rho) k⟨rho⟩
with transVal_ren {n} (v : Val n) {m} (xi : fin n -> fin m) 
  {p} (rho : fin m -> fin p)  : 
  (transVal v xi)⟨rho⟩ = transVal v (xi >> rho).
Proof. (* FILL IN HERE *) Admitted.

Lemma transTm_ren' {n} (e : Tm n) 
  (k : Val n) {p} (rho : fin n -> fin p)  : 
  (transTm e id k)⟨rho⟩ = transTm e⟨rho⟩ id k⟨rho⟩.
Proof.
  unfold_erewrite @transTm_ren.
  unfold_erewrite @transTm_ren_comp'.
  f_equal.
Qed.
  
  
Lemma transVal_ren' {n} (v : Val n) 
  {p} (rho : fin n -> fin p)  : 
  (transVal v id)⟨rho⟩ = transVal v⟨rho⟩ id.
Proof.
  unfold_erewrite @transVal_ren.
  unfold_erewrite @transVal_ren_comp'.
  f_equal.
Qed.

(** * Substitution lemma *)


(** tactic for accessibility proof *)
Ltac wf ACC := eapply (Acc_inv ACC); 
          try rewrite size_ren_Tm; try rewrite size_ren_Val; lia.

Fixpoint substitution_Tm {n} (e : Tm n) (w : Val n) {m}
  (σ σ' : fin n -> Val m) (ACC : Acc lt (size_Tm e)) { struct ACC } : 
    (σ' = (σ >> fun v => transVal v id)) ->
    (E{e} id w)[σ'] = E{ e[σ]} id (w[σ'])
with 
 substitution_Val {n}(v : Val n){m}  (σ σ' : fin n -> Val m)
    (ACC : Acc lt (size_Val v)) { struct ACC }: 
    (σ' = (σ >> fun v => transVal v id)) ->
    (V{v} id)[σ'] = V{ v[σ]} id
with 
 substitution_Stack {n}(s : list (Frame n)){m} (σ σ' : fin n -> Val m)
    (ACC : Acc lt (size_Stack s)) { struct ACC }: 
    (σ' = (σ >> fun v => transVal v id)) ->
    (S{s} id)[σ'] = S{ s[σ]} id.
Proof. (* FILL IN HERE *) Admitted.
 



(** Specialized version of substitution lemma for a top-level substitution *)
Lemma trans_Subst (e : Tm 1) (w : Val 1) (v : Val 0) :
 (E{e} ξ0⤉ w) [(V{v} ξ0)..] = E{ e[v..]}ξ0 (w[(V{v} ξ0)..]).
Proof.
  unfold_erewrite (@transTm_ren_comp' _ e); eauto.
  unfold ξ0.
  unfold_erewrite (@transTm_ren_comp' _ (e[v .: var])); eauto.
  unfold_erewrite @substitution_Tm ; eauto.
  2: eapply lt_wf.
  instantiate (1:= (v..)).
  2: {  unfold funcomp. extensionality x. destruct x. cbn. done.
        cbn. done. } 
  f_equal.
  asimpl. done.
Qed.
Lemma trans_Subst_Val (v1 : Val 1) (v : Val 0) :
 (V{v1} ξ0⤉) [(V{v} ξ0)..] = V{ v1[v..]}ξ0.
  unfold ξ0.
  unfold_erewrite (@transVal_ren_comp' _ v1); eauto.
  unfold_erewrite (@transVal_ren_comp' _ (v1[v .: var])); eauto.
  unfold_erewrite @substitution_Val ; eauto.
  2: eapply lt_wf.
  instantiate (1:= (v..)).
  2: {  unfold funcomp. extensionality x. destruct x. cbn. done.
        cbn. done. } 
  f_equal.
  asimpl. done.
Qed.


(** Substitution lemma in a lifted scope. We need this in the beta-case only. *)
Lemma trans_Subst_lift (e : Tm 1) (w : Val 2) (v : Val 0) : 
  (E{e} (ξ0 ⤉ >> ↑) w)[⇑ (V{v} ξ0)..] = E{e[v..]} ξ1 w[⇑ (V{v} ξ0)..].
Proof.
  unfold_erewrite @transTm_ren_comp'; eauto.
  unfold_erewrite (@transTm_ren_comp' _ (e[v .: var])); eauto.
  unfold_erewrite @substitution_Tm ; eauto.
  instantiate (1:= ⇑(v..)).
  f_equal.
  - unfold ξ1. unfold ξ0. asimpl. done.
  - unfold ξ0. unfold funcomp.
    eapply lt_wf; eauto.
  - extensionality f.
    destruct f. cbn. asimpl. unfold funcomp.
    destruct f. cbn. done. 
    cbn. unfold_erewrite @transVal_ren'; eauto.
    cbn. done.
Qed.




Fixpoint Kubstitution_Tm { n } (e : Tm n){m} (w : Val m) 
   (σ : fin m -> Val n) (θ : fin n -> fin m)  
   (ACC : Acc lt (size_Tm e)) { struct ACC } :
    (forall x, (θ >> σ) x = var x) -> 
     (E{e⟨θ⟩} id w)[σ] = E{e} id w[σ]
with Kubstitution_Val { n } (v : Val n){m} 
   (σ : fin m -> Val n) (θ : fin n -> fin m) 
   (ACC : Acc lt (size_Val v)) { struct ACC } :
    (forall x, (θ >> σ) x = var x) -> 
     (V{v⟨θ⟩} id)[σ] = V{v} id
with Kubstitution_Stack { n } (s : list (Frame n)){m} 
   (σ : fin m -> Val n) (θ : fin n -> fin m) 
   (ACC : Acc lt (size_Stack s )) { struct ACC } :
    (forall x, (θ >> σ) x = var x) -> 
     (S{s⟨θ⟩} id)[σ] = S{s} id.
Proof. (* FILL IN HERE *) Admitted.

Lemma kubstitution (e : Tm 0)(w : Val 1) (v : Val 0) :
    (E{e}ξ1 w)[v..] = E{e}ξ0 w[v..].
Proof.
  unfold_erewrite @transTm_ren_comp'.
  unfold_erewrite @Kubstitution_Tm. 2: eapply lt_wf.
  unfold ξ0. done.
  intros x. destruct x.
Qed.

(** * Semantic preservation *)

Lemma trans_step : 
  forall s1 (e1 : Tm 0) s2 e2,
  (s1, e1) ↦ (s2, e2) ->
  machine_ok (s1, e1) ->
  multi Small.step (E{e1}ξ0 S{s1}ξ0) (E{e2}ξ0 S{s2}ξ0).
Proof.
  intros s1 e1 s2 e2 h1 h2.
  inversion h1; inversion h2; subst.
  - inversion H0; subst; clear H0.
    all: invert_typing.
    all: cbn.
    + (* beta *)
      eapply ms_trans.
      eapply Small.s_let.
      eapply Small.s_prim.
      eapply s_beta.
      cbn.
      unfold_rewrite trans_Subst_lift.
      cbn.
      eapply ms_trans.
      eapply Small.s_let_ret.
      cbn.
      eapply ms_trans.
      eapply Small.s_prim.
      eapply s_beta.
      unfold_rewrite substFresh.
      unfold_rewrite kubstitution.
      eapply ms_refl.
    + (* ifz-zero *)
      eapply ms_trans.
      eapply Small.s_prim.
      eapply s_ifz_zero.
      eapply ms_refl.
    + (* ifz-succ *)
      eapply ms_trans.
      eapply Small.s_prim.
      eapply s_ifz_succ.
      unfold_rewrite trans_Subst.
      unfold_rewrite substFresh.
      eapply ms_refl.
    + (* prj1 *)
      eapply ms_trans.
      eapply Small.s_let.
      eapply Small.s_prim.
      eapply s_prj1.
      eapply ms_trans.
      eapply Small.s_let_ret.
      cbn.
      unfold_rewrite substFresh.
      eapply ms_refl.
    + (* prj2 *)
      eapply ms_trans.
      eapply Small.s_let.
      eapply Small.s_prim.
      eapply s_prj2.
      eapply ms_trans.
      eapply Small.s_let_ret.
      cbn.
      unfold_rewrite substFresh.
      eapply ms_refl.
    + (* case-inj1 *)
      eapply ms_trans.
      eapply Small.s_prim.
      eapply s_case_inj1.
      unfold_rewrite trans_Subst.
      unfold_rewrite substFresh.
      eapply ms_refl.
    + (* case-inj2 *)
      eapply ms_trans.
      eapply Small.s_prim.
      eapply s_case_inj2.
      unfold_rewrite trans_Subst.
      unfold_rewrite substFresh.
      eapply ms_refl.
    + (* app-rec *)
      eapply ms_trans.
      eapply Small.s_let.
      eapply Small.s_prim.
      eapply s_app_rec.
      replace (rec V{v}ξ0⤉) with (V{rec v}ξ0). 2: auto.
      unfold_rewrite trans_Subst_Val.
      eapply ms_refl.
    + (* prj1-rec *)
      eapply ms_trans.
      eapply Small.s_let.
      eapply Small.s_prim.
      eapply s_prj_rec.
      replace (rec V{v}ξ0⤉) with (V{rec v}ξ0). 2: auto.
      unfold_rewrite trans_Subst_Val.
      eapply ms_refl.
    + (* prj2-rec *)
      eapply ms_trans.
      eapply Small.s_let.
      eapply Small.s_prim.
      eapply s_prj_rec.
      replace (rec V{v}ξ0⤉) with (V{rec v}ξ0). 2: auto.
      unfold_rewrite trans_Subst_Val.
      eapply ms_refl.
    + (* unfold *)
      eapply ms_trans.
      eapply Small.s_let.
      eapply Small.s_prim.
      eapply s_unfold.
      eapply ms_trans.
      eapply Small.s_let_ret.
      cbn.
      unfold_rewrite substFresh.
      eapply ms_refl.
  - (* s_pop *)
    cbn.
    eapply ms_trans.
    eapply Small.s_prim.
    eapply s_beta.
    unfold_rewrite trans_Subst.
    unfold_rewrite substFresh.
    eapply ms_refl.
  - (* s_push *) 
    cbn.
    eapply ms_refl.
  - (* s_letcc *)
    cbn.
    eapply ms_trans.
    eapply Small.s_let_ret.
    replace (S{s2} ξ0) with (V{cont s2}ξ0) at 1; auto.
    unfold_rewrite trans_Subst.
    unfold_rewrite substFresh.
    eapply ms_refl.
  - (* s_throw *)
    cbn. fold (@transStack 0).
    eapply ms_refl.
  - (* s_exit *)
    cbn.
    eapply ms_refl.
Qed.


