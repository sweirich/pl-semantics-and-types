From Stdlib Require Import Psatz.
From Stdlib Require Import Arith.

Require Import rec.iprop.
Require Import untyped.stack.

Require Export untyped.equiv.
Require Export untyped.contextual.

Import SyntaxNotations.
Import Lists.List.ListNotations.
Import untyped.stack.Notations.
Import rec.iprop.Notations.

Open Scope iProp_scope.
Open Scope list_scope.
Open Scope rec_scope.

Import FinValues.

Module Notations.
Notation "e <=CTX e'" := (CTX _ e e') (at level 70).
Notation "e <=CTX e'" := (CTX _ e e') (at level 70).
Notation "e <=CIU e'" := (CIU _ e e') (at level 70).
Notation "e <=log e'" := (logtm _ e e') (at level 70).
End Notations.

Import Notations.

(** * "Beta" reduction rules. *)

(*  X |- (\x. e)v <= e[v/x] *)
Lemma fun_beta n (e : Tm (S (S n))) (v : Val n) :
  (app (abs e) v) <=CIU e[v .: (abs e)..].
Proof.
  intros σ s.
  cbn.
  intro h.
  eapply halts_forward in h.
  2: { eapply Small.s_prim. eapply s_beta. } 
  asimpl in h.
  done.
Qed.

Lemma ifz_zero_beta n (e1 : Tm n) e2 :
  ifz zero e1 e2 <=CIU e1.
Proof.
  intros σ s.
  cbn.
  intro h.
  eapply halts_forward in h. 
  2: { eapply Small.s_prim. eapply s_ifz_zero. } 
  done.
Qed.                           

Lemma ifz_succ_beta n v (e1 : Tm n) e2 :
  ifz (succ v) e1 e2 <=CIU e2 [ v .. ] .
Proof.
  intros σ s.
  cbn.
  intro h.
  eapply halts_forward in h. 
  2: { eapply Small.s_prim. eapply s_ifz_succ. } 
  asimpl in h.
  done.
Qed.                           

Lemma let_ret n (e : Tm (S n)) v : 
  let_ (ret v) e <=CIU e[v..].
Proof.
  intros σ s.
  cbn.
  intro h.
  eapply halts_forward in h.
  2: { eapply Small.s_push. } 
  eapply halts_forward in h.
  2: { eapply Small.s_pop. } 
  asimpl in h.
  done.
Qed.


Lemma fun_beta_expand n (e : Tm (S (S n))) (v : Val n) :
   e[v .: (abs e)..] <=CIU (app (abs e) v).
Proof.
  intros σ s.
  cbn.
  intro h.
  eapply halts_reverse.
   2: { eapply Small.s_prim. eapply s_beta. } 
  asimpl in h.
  done.
Qed.

Lemma ifz_zero_beta_expand n (e1 : Tm n) e2 :
  e1 <=CIU ifz zero e1 e2.
Proof.
 intros σ s.
 cbn.
 intro h.
 eapply halts_reverse.
 2: { eapply Small.s_prim. eapply s_ifz_zero. } 
 done.
Qed.

Lemma ifz_succ_beta_expand n v (e1 : Tm n) e2 :
  e2 [ v .. ] <=CIU ifz (succ v) e1 e2.
Proof.
  intros σ s.
  cbn.
  intro h.
  eapply halts_reverse. 
  2: { eapply Small.s_prim. eapply s_ifz_succ. } 
  asimpl in h.
  done.
Qed.                           

Lemma let_ret_expand n (e : Tm (S n)) v : 
  e[v..] <=CIU let_ (ret v) e.
Proof.
  intros σ s.
  cbn.
  intro h.
  eapply halts_reverse.
  2: { eapply Small.s_push. } 
  eapply halts_reverse.
  2: { eapply Small.s_pop. } 
  asimpl in h.
  done.
Qed.


  

(** * "Eta" reduction rules. *)

(*  X |- \x. v x == v *)
(* Uses logical relation *)
Lemma fun_eta n (v : Val n) :
  logval n (abs (app v⟨↑⟩⟨↑⟩ (var f0))) v.
Proof.
  unfold logval.
  intros k σ1 σ2 Es.
  cbn.
  rewrite V_def.
  intros v1 v1' j LEj. next j.
  intros Vvv.
  asimpl.
  eapply C_app.
  have Ev: logval n v v. eapply scoped_refl. typeclasses eauto.
  unfold logval in Ev.
  eapply Ev. eapply dclosed; eauto. lia.
  auto.
Qed.


Lemma nat_eta n (v : Val n) :
  logtm n (ifz v (ret zero) (ret (succ (var var_zero)))) (ret v).
Proof.
  unfold logtm.
  intros k σ1 σ2 Es.
  cbn.
  have EV: logval n v v. eapply scoped_refl. typeclasses eauto.
  rewrite C_def.
  intros s s' j LEj StE. 
  rewrite St_def in StE.
  intros [v1 h].
  inversion h; subst; clear h.
  inversion H; subst; clear H.
  destruct v[σ1] eqn:EQH;
  auto_unfold in *; rewrite EQH in H4; inversion H4; subst; clear H4.
  - specialize (EV k0 σ1 σ2).
    specialize (StE zero v[σ2] k0 ltac:(lia)).
    eapply StE.
    rewrite <- EQH.
    eapply EV.
    eapply dclosed; eauto.
    lia.
    exists v1. eauto.
  - cbn in H0.
    unfold logval in EV.
    specialize (EV k _ _ Es). 
    auto_unfold in *. rewrite EQH in EV.
    rewrite V_def in EV. destruct v[σ2] eqn: EQH2.
    all: auto_unfold in *; rewrite EQH2 in EV; try done.
    eapply StE.
    3: { exists v1. eapply H0. }  lia.
    auto_unfold in *. rewrite EQH2.
    rewrite V_def.
    eapply dclosed; eauto. lia.
Qed.


(** * failure of eta-expansion rules *)


(* The opposite is not true because we don't have types. For example 
   v could be "0". *)
Lemma not_fun_eta_expand :
  not (forall (v : Val 0), ContextualVal _ v (abs (app v⟨↑⟩⟨↑⟩ (var f0)))).
Proof.
  intros h.
  specialize (h zero).
  unfold ContextualVal in h.
  specialize (h (c_ifz1 c_hole (ret zero) (ret zero))).
  cbn in h.
  have PRE: Small.halts ([], ifz zero (ret zero) (ret zero)). eexists. eapply ms_trans.
  eapply Small.s_prim. eapply s_ifz_zero. eapply ms_refl.
  specialize (h PRE). clear PRE.
  destruct h as [v h1].
  inversion h1. subst. clear h1.
  inversion H. subst. clear H.
  inversion H4.
Qed.

(** * Beta equivalence implies contextual/oberservational equivalence. But does not relate as many terms *)

Reserved Notation "t1 =β t2" (at level 70).
Reserved Notation "t1 =vβ t2" (at level 70).

Inductive BE (n : nat) : Tm n -> Tm n -> Prop :=
  | BE_beta : forall (e : Tm _) (v : Val _), 
      app (abs e) v =β e[v .: (abs e)..]
  | BE_ifz_zero : forall (e1 : Tm n) (e2 : Tm (S n)), 
      ifz zero e1 e2 =β e1
  | BE_ifz_succ : forall (e1 : Tm n) (e2 : Tm (S n)) (k : Val n), 
      ifz (succ k) e1 e2 =β e2[k..]

  | BE_letv v e : 
      let_ (ret v) e =β e[v ..]
  | BE_ret v1 v2 : 
      (BV _ v1 v2) -> ret v1 =β ret v2
  | BE_let e1 e2 e1' e2' : 
      e1 =β e2 -> e1' =β e2' -> let_ e1 e1' =β let_ e2 e2'
  | BE_app v1 v2 v1' v2' : 
      v1 =vβ v2 -> v1' =vβ v2' -> app v1 v1' =β app v2 v2'
  | BE_ifz v1 v2  e1 e2 e1' e2' : 
      v1 =vβ v2 -> e1 =β e2 -> e1' =β e2' -> ifz v1 e1 e1' =β ifz v2 e2 e2'
  | BE_trans e1 e2 e3 : 
      e1 =β e2 -> e2 =β e3 -> e1 =β e3
  | BE_sym  e1 e2 : 
      e1 =β e2 -> e2 =β e1
with BV (n : nat) : Val n -> Val n -> Prop := 
  | BV_var x : (var x) =vβ (var x)
  | BV_unit : unit =vβ unit 
  | BV_zero : zero =vβ zero
  | BV_succ v1 v2 : v1 =vβ v2 -> succ v1 =vβ succ v2
  | BV_abs e1 e2 : e1 =β e2 -> abs e1 =vβ abs e2


where "t1 =β t2" := (BE _ t1 t2)
  and "t1 =vβ t2" := (BV _ t1 t2)
.

(** * logical equivalence *)

Definition eqtm n e1 e2 := logtm n e1 e2 /\ logtm n e2 e1.
Definition eqval n v1 v2 := logval n v1 v2 /\ logval n v2 v1.

Instance Compatible_eqtm : Compatible eqtm eqval.
constructor.
all: intros.
all: split.
all: try match goal with [H : eqval _ _ _ |- _ ] => move: H => [h1 h2] end.
all: try match goal with [H : eqval _ _ _ |- _ ] => move: H => [h3 h4] end.
all: try match goal with [H : eqtm _ _ _ |- _ ] => move: H => [h5 h6] end.
all: try match goal with [H : eqtm _ _ _ |- _ ] => move: H => [h7 h8] end.
- eapply logvar; eauto.
- eapply logvar; eauto.
- eapply logunit; eauto.
- eapply logunit; eauto.
- eapply logzero.
- eapply logzero.
- eapply logsucc; eauto.
- eapply logsucc; eauto.

- eapply logabs; eauto.
- eapply logabs; eauto.

- eapply logret; eauto.
- eapply logret; eauto.
- eapply loglet; eauto. 
- eapply loglet; eauto. 
- eapply logifz; eauto.
- eapply logifz; eauto.

- eapply logapp; eauto.
- eapply logapp; eauto.

Qed.

Instance Reflexive_eqtm : ScopedReflexive eqtm.
split. eapply scoped_refl. typeclasses eauto.
eapply scoped_refl. typeclasses eauto.
Qed.

Instance Reflexive_eqval : ScopedReflexive eqval.
split. eapply scoped_refl. typeclasses eauto.
eapply scoped_refl. typeclasses eauto.
Qed.

Instance Transitive_eqtm : ScopedTransitive eqtm.
intros ? ? ? ? [h1 h1'][h2 h2']. split.
  eapply scoped_trans; eauto. 
  eapply scoped_trans; eauto. 
Qed.

(** * Beta equivalence implies logical equivalence *)

Fixpoint BE_subrelation n e1 e2 : 
  BE n e1 e2 -> eqtm n e1 e2
with BV_subrelation n e1 e2 : 
  BV n e1 e2 -> eqval n e1 e2.
Proof.  
  + intro h. inversion h; subst.
  - split; eapply CIU_logtm.
    eapply fun_beta.
    eapply fun_beta_expand.
  - split. 
    eapply CIU_logtm.
    eapply ifz_zero_beta.
    eapply CIU_logtm.
    eapply ifz_zero_beta_expand.
  - split.
    eapply CIU_logtm.
    eapply ifz_succ_beta.
    eapply CIU_logtm.
    eapply ifz_succ_beta_expand.

  - split.
    eapply CIU_logtm.
    eapply let_ret.
    eapply CIU_logtm.
    eapply let_ret_expand.
  - eapply comp_ret; eauto. 
  - eapply comp_let; eauto.
  - eapply comp_app; eauto.
  - eapply comp_ifz; eauto.
  - eapply scoped_trans. eapply BE_subrelation. eapply H.
    eapply BE_subrelation. eapply H0.
  - apply BE_subrelation in H. destruct H as [h1 h2].
    split. auto. auto.
  + intro h. inversion h.
    eapply val_var; eauto.
    eapply val_unit; eauto.
    eapply val_zero; eauto.
    eapply val_succ; eauto.
    eapply val_abs; eauto.

Qed.




 
