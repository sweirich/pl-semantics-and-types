(** This development is adapted from Andy Pitts, 
    "Step-Indexed Biorthogonality: a Tutorial Example" 

    It demonstrates the use of a step-indexed logical 
    relation to define contextual equivalence for the 
    untyped lambda calculus.

    The key ideas are 

     (1) Definition of "Contextual" preorder as the largest 
           adequate, compatible preorder
     (2) Definition of "CIU" preorder 
           what terms look the same with all stacks (uses), 
           and after all substitutions (closing instantiations)
     (3) Use of a step-indexed "logical" preorder to show
           the equivalence between the two definitions    

*)

From Stdlib Require Import Psatz.
From Stdlib Require Import Arith.

Require Export common.core.
Require Export untyped.stack.
Require Export rec.iprop.

Require Export untyped.ctx.

Import SyntaxNotations.
Import Lists.List.ListNotations.
Import stack.Notations.
Import rec.iprop.Notations.

Open Scope list_scope.
Open Scope rec_scope.

(* -------------------------------------------------------- *)

(** * Closed instantiations (of uses) *)

Definition ciu : Tm 0 -> Tm 0 -> Prop := 
  fun e e' => 
    forall s, Small.halts (s, e) -> Small.halts (s, e').

Definition CIU : scoped_relation Tm := 
  fun n e e' => 
    forall σ, ciu e[σ] e'[σ].

(* By definition CIU is an adequate pre-order *)

Instance Adequate_CIU : Adequate CIU.
Proof.
  intros e e' h.
  unfold CIU, ciu in h.
  unfold Small.halts.
  specialize (h ids nil).
  asimpl in h.
  done.
Qed.

Instance Reflexive_CIU : Reflexive CIU.
  constructor.
  - intros n t. unfold CIU, ciu.
    done.
Qed.

Instance Transitive_CIU : Transitive CIU.
Proof.
  constructor.
  - intros n t1 t2 t3.
    unfold CIU, ciu.
    intros h1 h2 s E.
    specialize (h1 s E).
    specialize (h2 s E).
    intro h; eauto.
Qed.


(** To show that CIU is compatible, we need to show that 
    it is equivalent to an obviously compatible
    logical relation. *)


(*** ------------------ **)

(** * Step-indexed logical relation *)


(* Step-indexed relation *)
Fixpoint V (v v' : Val 0) k {struct k} : Prop := 
  let fix St (s s' : stack) k := 
    ▷ (St s s') k /\
    forall v v', (V v v') k ->
            (fun k => Small.halts_n (s, ret v) k -> Small.halts (s', ret v')) k
  in
  let fix C (e e' : Tm 0) k := 
    ▷ (C e e') k /\
    forall s s' , (St s s') k ->
             (fun k => Small.halts_n (s, e) k -> Small.halts (s', e')) k
  in
   match v , v' with 
   | unit, unit => True
   | zero, zero => True
   | succ v1 , succ v2 => 
       ▷ (V v1 v2) k
   | abs e , v2 => 
       ▷ (V v v') k /\
       forall v1 v1', (▷ (V v1 v1') k ->
                  ▷ (C e[v1 .: (abs e)..] (app v2 v1')) k)

   | _ , _ => False
   end.

Fixpoint St (s s' : stack) k := 
    ▷ (St s s') k /\
    forall v v', (V v v') k ->
            (fun k => Small.halts_n (s, ret v) k -> 
                   Small.halts   (s', ret v')) k.
Fixpoint C (e e' : Tm 0) k := 
    ▷ (C e e') k /\
    forall s s' , (St s s') k ->
             (fun k => Small.halts_n (s, e) k -> Small.halts (s', e')) k.

(* extended to open relations by closing over 
   related substitutions *)

Definition eqsig n (σ σ' : fin n -> Val 0) k :=
    forall x, V (σ x) (σ' x) k.

Definition eqval n (v v' : Val n) := 
  forall k σ σ' , eqsig n σ σ' k -> V v[σ] v'[σ'] k.

Definition eqtm  n (e e' : Tm n) := 
  forall k σ σ' , eqsig n σ σ' k -> C e[σ] e'[σ'] k.
  
Definition eqst (s s' : stack) := 
  forall k, St s s' k.

(** * All step-indexed definitions are downward closed. *)

Instance DownC e e' : IProp (C e e').
constructor.  
induction k.
intros hC j LEj. inversion LEj. done.
intros hC j LEj. inversion LEj. done.
subst. cbn in hC. move: hC => [hC _].
eapply IHk; eauto. 
Qed.

Instance DownSt E E' : IProp (St E E').
constructor.
induction k.
intros hC j LEj. inversion LEj. done.
intros hC j LEj. inversion LEj. done.
subst. cbn in hC. move: hC => [hC _].
eapply IHk; eauto. 
Qed.

Instance DownV v v' : IProp (V v v').
constructor. move=> k. 
move: v v'. 
induction k; intros v v'.
intros hC j LEj. inversion LEj. done.
intros hC j LEj. inversion LEj. done.
subst. 
destruct v; destruct v'; try done.
all: cbn in hC.
all: try solve [next j; eapply IHk; eauto; lia].
all: try solve [destruct hC; eapply IHk; eauto].
all: try solve [destruct hC;
  next j; split; [eauto | eapply IHk; auto]; lia].
- next j. done.
- next j. done.

Qed.

Instance Down_eqsig n σ σ' : IProp (eqsig n σ σ').
constructor. 
unfold eqsig.
intros k EQ j LE x.
eapply dclosed; eauto.
Qed.

(** * Convenience functions for unfolding the logical relation *)

Lemma St_def : forall s s' k, 
  St s s' k <-> 
  (forall v v' , ((V v v') ⇒ 
              (fun k => Small.halts_n (s, ret v) k -> Small.halts (s', ret v'))) k).
Proof.
  move=> E E'.
  elim /strong_ind. intros k ih.
  split.
  - intros StEE.
    intros v v' j LEj Vvv'.
    inversion LEj. subst.
    + destruct k; cbn in StEE;
      move: StEE => [_ h];
      specialize (h v v'); eapply h; eauto.
    + subst.
      specialize (ih j ltac:(lia)).
      move: ih => [h1 h2].
      eapply h1; eauto.
      eapply dclosed; eauto.
  - intros h.
    destruct k.
    + split; auto. done.
      intros v v' Vv'. eapply h; eauto.
    + split; auto. cbn.
      specialize (ih k ltac:(auto)). rewrite ih.
      intros v v' j LEj. eapply h; eauto.
      intros v v' Vvv'. eapply h; eauto.
Qed.
    
Lemma C_def (e e' : Tm 0) k :
 C e e' k <->  
   (forall s s' , ((St s s') ⇒ 
              (fun k => Small.halts_n (s, e) k -> Small.halts (s', e'))) k).
Proof. 
  move: k.
  elim /strong_ind. intros k ih.
  split.
  - intros Cee'.
    intros E E' j LEj StEE'.
    inversion LEj; subst.
    + destruct k; eapply Cee'; auto.
    + specialize (ih j ltac:(lia)).
      eapply ih; eauto.
      eapply dclosed; eauto.
  - intros h.
    destruct k; split; auto. 
    done.
    intros E E' StEE'.
    eapply h; eauto.
    specialize (ih k ltac:(auto)). cbn. rewrite ih.
    intros E E' j LEj. eapply h; eauto.
    intros E E' StEE'. eapply h; eauto.
Qed.

Lemma V_def_abs e v2 k :
   V (abs e) v2 k <-> 
        forall v v', (▷ (V v v') ⇒ ▷ (C e[v .: (abs e)..] (app v2 v'))) k.
move: k.
elim /strong_ind. intros k ih.
split.
- intro Vabs.
  intros v v' j LEj Vvv'.
  next j. cbn in Vvv'.
  inversion LEj. subst.
  + cbn in Vabs. fold St C in Vabs. move: Vabs => [Vabs h].
    eapply h; eauto.
  + subst. specialize (ih (S j) ltac:(lia)).
    move: ih => [h _].
    apply dclosed with (j:= S j) in Vabs. 2: lia.
    specialize (h Vabs v v' (S j) ltac:(auto) Vvv'). 
    cbn. done.
- intros h. 
  next k. fold St C.
  specialize (ih k ltac:(eauto)). 
  split.
  + rewrite ih.
    intros v v' j LEj Vvv'. eapply h; eauto.
  + intros v v' Vvv'.
    specialize (h v v' (S k) ltac:(lia)). cbn in h. auto.
Qed.


Lemma V_def (v v' : Val 0) k :
  V v v' k <->
   match v , v' with 
   | unit , unit => True 
   | zero  , zero => True
   | succ v1 , succ v2 => ▷ (V v1 v2) k
   | abs e , _ => 
       forall v1 v1', (▷ (V v1 v1') ⇒ ▷ (C e[v1 .: (abs e)..] (app v' v1'))) k

   | _ , _ => False
   end.
Proof.
  destruct v eqn:EV. 
  all: try solve [destruct k; cbn; done].
  rewrite V_def_abs. done.
Qed.



(** * Computation relation is closed under reverse eval *)

Lemma reverse_prim2 e1 e2 e2' k : 
  C e1 e2' k -> e2 ~>> e2' -> C e1 e2 k.
Proof.
  repeat rewrite C_def.
  intros h hSS.
  intros E E' j LEj StEE hEe1.
  specialize (h _ _ j LEj StEE hEe1).
  eapply Small.halts_reverse_prim; eauto.
Qed.


(** Two congruence lemmas for working with f_let frames and let_ terms *)

Lemma E_LET_cong k e e' (s s' : stack) : 
  (forall v v', (▷ (V v v') ⇒ ▷ (C e[v..] e'[v'..])) k) ->
  ((St s s' ⇒ St (f_let e :: s) (f_let e' :: s')) k).
Proof.
  intro h17. 
  intros j LEj Sts.
  rewrite St_def.
  intros v v' i LEi VVi hH.
  edestruct @halts_n_forward with (m' := (s, e[v..])) as [k0 [EQ hH']]; 
    eauto using Small.step. subst.

  move: (h17 v v' (S k0) (ltac:(lia))) => h1. cbn in h1.
  apply dclosed with (j := k0) in VVi; auto. 
  specialize (h1 VVi). rewrite C_def in h1.
  specialize (h1 s s' k0 ltac:(auto) ltac:(eapply dclosed; eauto; lia)).
  cbn in h1.
  eapply halts_reverse; eauto using stack.Small.step.
Qed.


Lemma E_let_cong k e e' e1 e1' : 
  (forall v v', (▷ (V v v') ⇒ ▷ (C e[v..] e'[v'..])) k) ->
  ((C e1 e1' ⇒ C (let_ e1 e) (let_ e1' e')) k).
Proof. 
  intro h17. 
  intros j LEj hE.
  rewrite C_def.
  rewrite C_def in hE.
  intros s s' i LEi EEi hH.
  move: (E_LET_cong k e e' s s' h17) => hSt.

  eapply @halts_n_forward with (m' := (f_let e :: s, e1)) in hH;
    eauto using Small.step.  
  edestruct hH as [k0 [<- h2]].

  specialize (hSt k0 ltac:(lia) ltac:(eapply dclosed; eauto; lia)). 
  rewrite St_def in hSt.

  move: (hE (f_let e :: s) (f_let e' :: s') k0 ltac:(lia)) => he1.
  have StLET: St (f_let e :: s) (f_let e' :: s') k0.
  { rewrite St_def. intros v v' m LEm VVm hLET.
    inversion hLET.
    eapply hSt; eauto.
  } 
  specialize (he1 StLET h2).

  eapply Small.halts_reverse; eauto using Small.step.
Qed.

(** * Compatibility rules: values *)

Lemma eqvar n x : eqval n (var x) (var x).
Proof.
intros k σ σ' Es.
cbn. unfold eqsig in Es. eauto.
Qed.

Lemma eqzero n : eqval n zero zero.
Proof.
intros k σ σ' Es.
cbn. unfold eqsig in Es. eauto.
next k. done.
Qed.

Lemma equnit n : eqval n unit unit.
Proof.
intros k σ σ' Es.
cbn. unfold eqsig in Es. eauto.
next k. done.
Qed.

Lemma eqsucc n v v' : 
  eqval n v v' -> 
  eqval n (succ v) (succ v').
Proof.
intro h.
intros k σ σ' Es.
cbn. unfold eqsig in Es.
next k. eapply h. unfold eqsig.
intros x. eapply dclosed. eauto. lia.
Qed.

Lemma subst_rewrite : forall {n} (σ : fin n -> Val 0) (e : Tm (S (S n)))  (v1 v2 : Val 0), 
    e [⇑ (⇑ σ)][v1 .: v2..] = e [v1 .: (v2 .: σ)].
intros.
asimpl.
done.
Qed.


Lemma eqabs n e e' : 
  eqtm _ e e' ->
  eqval n (abs e) (abs e').
Proof.
intro h.
unfold eqval.
(** we need to use strong induction because of recursive functions *)
elim /strong_ind. intros k ih.
intros σ σ' Es.
cbn. rewrite V_def_abs.
intros v v' j LEj Vv.
rewrite subst_rewrite.
next j.
cbn in Vv.
eapply reverse_prim2. 2: { econstructor. } 
rewrite subst_rewrite.
eapply h.
unfold eqsig.
intro x. destruct x; cbn; auto.
destruct f; cbn; auto.
eapply dclosed with (j:=j) in Es; eauto.
lia. 
specialize (ih j ltac:(lia) σ σ' ltac:(eapply dclosed; eauto; try lia)).
cbn in ih.
done.
Qed.



(** * Compatibility rules: terms *)

Lemma eqret n v v' : 
  eqval n v v' 
  -> eqtm n (ret v) (ret v').  
Proof.
(* FILL IN HERE *) Admitted.


(* Application is congruence *)
Lemma eqapp n v1 v1' v2 v2' : 
  eqval n v1 v1' -> eqval n v2 v2' ->
  eqtm n (app v1 v2) (app v1' v2').
Proof.
(* FILL IN HERE *) Admitted.

Lemma eqlet n e1 e1' e2 e2' : 
  eqtm n e1 e1' -> eqtm (S n) e2 e2' -> 
  eqtm n (let_ e1 e2) (let_ e1' e2').
Proof.
(* FILL IN HERE *) Admitted.


Lemma eqifz n v v' e0 e0' e1 e1' : 
  eqval n v v' -> eqtm n e0 e0' -> eqtm _ e1 e1' -> 
  eqtm _ (ifz v e0 e1) (ifz v' e0' e1').
Proof. 
(* FILL IN HERE *) Admitted.



Instance compat_eq : Compatible eqtm eqval.
constructor.
- eapply eqvar.
- eapply equnit.
- eapply eqzero.
- eapply eqsucc.

- eapply eqabs.

- eapply eqret. 
- eapply eqlet.
- eapply eqifz.

- eapply eqapp.

Qed.

(* --------------------------------------------- *)

(** Because the logical relation is compatible, it is also 
    reflexive. This is our fundamental property of the 
    logical relation. *)

Corollary refl_val n v : eqval n v v.
Proof.
  eapply scoped_refl; eauto.
Qed.
Corollary refl_tm n e : eqtm n e e.
Proof.
  eapply scoped_refl; eauto.
Qed.

Lemma refl_sig n s : forall k, eqsig n s s k.
Proof.
  intros k. unfold eqsig. 
  intros x.
  move: (refl_val 0 (s x)) => h.
  unfold eqval in h.
  specialize (h k ids ids). asimpl in h.
  eapply h.
  unfold eqsig. auto_case.
Qed.

Lemma refl_St E : eqst E E.
Proof.
(* FILL IN HERE *) Admitted.

(* --------------------------------------------- *)

(* Now that we have shown that the logical relation is 
   reflexive, we can show that it is equivalent to CIU *)

(** * Logical  preorder implies CIU pre-order *)
Lemma eqtm_CIU n e e' : 
  eqtm n e e' -> CIU n e e'.
Proof.
(* FILL IN HERE *) Admitted.

(** * Logical preorder is closed under CIU *)
Lemma eqtm_closed_CIU n e e' e'' :
  eqtm n e e' -> CIU n e' e'' -> eqtm n e e''.
Proof. 
(* FILL IN HERE *) Admitted.


(** * CIU Pre-order implies logical preorder *)
Lemma CIU_eqtm n e e' : 
  CIU n e e' -> eqtm n e e'.
Proof.
  intros h.
  move: (refl_tm n e) => hE.
  eapply eqtm_closed_CIU; eauto.
Qed.


(* -------------------------------------------- *)

(** Because CIU is equivalent to to logical equivalence, we can 
now show that it is compatible. *)

Instance Compatible_CIU : Compatible CIU eqval.
constructor.
- eapply eqvar; eauto.
- eapply equnit; eauto.
- eapply eqzero; eauto.
- eapply eqsucc; eauto.

- intros n e1 e2 CIU.
  eapply eqabs.
  eapply CIU_eqtm; auto.

- intros.
  eapply eqtm_CIU.
  eapply eqret; eauto.
- intros.
  eapply eqtm_CIU.
  eapply eqlet; eauto using CIU_eqtm.
- intros. 
  eapply eqtm_CIU.
  eapply eqifz; eauto using CIU_eqtm.

- intros.
  eapply eqtm_CIU.
  eapply eqapp; eauto.

Qed.

(** Compatibilility was the last piece of showing that 
    CIU implies CTX. *)

Lemma CIU_CTX n e e' : 
  CIU n e e' -> CTX n e e'.
Proof.
  intros h.
  econstructor; eauto.
  - eapply Compatible_CIU.
  - eapply Adequate_CIU.
  - eapply Transitive_CIU.
Qed.


(* -------------------------------------------- *)

(* TO Show that CTX implies CIU, we need to know that 
   CTX is closed under substitution. *)


(* We show this by induction on the length of the substitution. 
   For a single step, we use the transtivity of CTX to 
   make the chain:

       e[v..] == (let (ret v) e) == (let (ret v) e') == e'[v..]
 *)

Lemma substitutivity n e e' v : 
  CTX (S n) e e' ->
  CTX n e[v..] e'[v..].
Proof.
  intro h.
  have C1: CTX n (let_ (ret v) e) (let_ (ret v) e').
  { 
    destruct h.
    econstructor; eauto.
    eapply comp_let.
    eapply comp_ret.
    eapply scoped_refl; eauto.
    done.
  } 
  have C2 : CTX n e[v..] (let_ (ret v) e).
  { 
    eapply CIU_CTX.
    unfold CIU. intros s.
    unfold ciu.
    intros E.
    asimpl.
    intro h1.
    eapply halts_reverse; 
      [| eauto using stack.Small.step, primitive].
    eapply halts_reverse; 
      [| eauto using stack.Small.step, primitive].
    asimpl.
    done.
  } 
  have C3 : CTX n (let_ (ret v) e') e'[v..].
  { 
    eapply CIU_CTX.
    unfold CIU. intros s.
    unfold ciu.
    intros E.
    asimpl.
    intro h1.
    eapply halts_forward in h1;  
      [| eauto using stack.Small.step, primitive].
    eapply halts_forward in h1;  
      [| eauto using stack.Small.step, primitive].
    asimpl in h1.
    done.
  } 
  eapply scoped_trans; eauto.
  eapply scoped_trans; eauto.
Qed.


Lemma split_sigma (n : nat) (e : Tm (S n)) (σ : fin (S n) -> Val 0) :
  e[(σ var_zero)⟨null⟩..][↑ >> σ] = e[σ].
Proof. 
  asimpl.
  rewrite idSubst_Val. auto_case.
  asimpl.
  auto.
Qed.

Lemma value_substitutivity n e e' : 
  CTX n e e' -> 
  forall σ, CTX 0 e[σ] e'[σ].
Proof.
  move: e e'.
  induction n.
  all: intros e e' h σ.
  - auto_unfold. 
    repeat rewrite idSubst_Tm; try auto_case. auto.
  - remember ((σ var_zero)⟨null⟩ : Val n) as v.
    specialize (IHn e[v..] e'[v..]).
    have h1:  CTX n e[v..] e'[v..].
    { eapply substitutivity; eauto. } 
    specialize (IHn h1 (↑ >> σ)).
    rewrite Heqv in IHn.
    repeat rewrite split_sigma in IHn.
    auto.    
Qed.

Lemma halts_LET s e' e : 
  Small.halts (f_let e' :: s, e) <-> Small.halts (s,let_ e e').
Proof.
  split.
  - intro h. eapply halts_reverse; 
      eauto using stack.Small.step, primitive.
  - intro h. eapply halts_forward; 
      eauto using stack.Small.step, primitive.
Qed.

Lemma CTX_ciu e e' :
  CTX 0 e e' -> ciu e e'.
Proof. 
  intros h.
  inversion h. clear h.
  unfold ciu.
  intros s.
  move: e e' H2.
  induction s; intros e e' Re.
  - specialize (H0 _ _ Re) => A.
    eauto.
  - destruct a.
    repeat rewrite halts_LET.
    intro h1.
    move: (@comp_let _ _ H) => CC.
    have Rtt: RE 1 t t. eapply scoped_refl.
    specialize (CC 0 e e' t t Re Rtt).
    move: (IHs _ _ CC) => h2.
    auto.
Qed.


Lemma CTX_CIU n e e' :
  CTX n e e' -> CIU n e e'.
Proof. 
  intros h.
  unfold CIU.
  intros σ.
  eapply CTX_ciu.
  eapply value_substitutivity.
  eauto.
Qed.


(** -------------------------------------------------------- *)

(** Now we have that all of our preorders are equivalent. *)

Lemma eqtm_CTX n e e' : 
  eqtm n e e' -> CTX n e e'.
Proof. intro h. eapply CIU_CTX. eapply eqtm_CIU. auto. Qed.
Lemma CTX_eqtm n e e' :
  CTX n e e' -> eqtm n e e'.
Proof. intro h. eapply CIU_eqtm. eapply CTX_CIU. auto. Qed.


Instance Compatible_CTX : Compatible CTX eqval.
constructor.
- eapply eqvar; eauto.
- eapply equnit; eauto.
- eapply eqzero; eauto.
- eapply eqsucc; eauto.

- intros n e1 e2 CTX.
  eapply eqabs.
  eapply CTX_eqtm; auto.

- intros.
  eapply eqtm_CTX.
  eapply eqret; eauto.
- intros.
  eapply eqtm_CTX.
  eapply eqlet; eauto using CTX_eqtm.
- intros. 
  eapply eqtm_CTX.
  eapply eqifz; eauto using CTX_eqtm.

- intros.
  eapply eqtm_CTX.
  eapply eqapp; eauto.

Qed.


(** -------------------------------------------------------- *)

