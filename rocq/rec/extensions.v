Require Export rec.typing.
Import typing.Notations.

(** Definitions for f0, f1, f2, etc *)
Import FinValues.

(** Derived forms for fine-grained CBV:

    We can define abbreviations for "normal" lambda calculus terms, 
    which do not include value restrictions, by using eagerlet. 

    For each of the derived forms, we prove lemmas about 
    substitution, typing and the operational semantics.

 *)

(** eager let: if e1 is a value, substitute, otherwise 
    create a let expression *) 

Definition eagerlet {n} (e1 : Tm n) (e2 : Tm (S n)) :=
  match e1 with 
  | ret v => e2[v..]
  | _ => let_ e1 e2
  end.

(** derived substitution rewrite *)
Lemma eagerlet_subst {m n : nat} (σ : fin n -> Val m) (e1 : Tm n) (e2 : Tm (S n)) :
   (eagerlet e1 e2)[σ] = eagerlet (e1[σ]) (e2[⇑ σ]).
Proof. 
  destruct e1; cbn; try reflexivity. now asimpl.
Qed.


(** derived typing rule for eager let term *)
Lemma t_eagerlet {n} Γ :
  forall (e1 : Tm n) (e2 : Tm (S n)) (τ1 τ2 : Ty 0), 
    Γ |-e e1 ∈ τ1 -> τ1 .: Γ |-e e2 ∈ τ2 -> Γ |-e eagerlet e1 e2 ∈ τ2.
Proof. 
  intros. unfold eagerlet.
  destruct e1; eauto.
  (* case for values *) inversion H.
  eapply substitution_tm; eauto with rec.
  (* all other cases, use typing rules in hint database *)
  all: eauto with rec.
Qed.


Lemma eagerlet_retv (v : Val 0) (e2 : Tm 1) :
  eagerlet (ret v) e2 = e2[v ..].
Proof.
  unfold eagerlet. auto.
Qed.

Lemma ms_eagerlet_cong (e1 e1' : Tm 0) (e2 : Tm 1) :
  e1 ~>* e1' -> eagerlet e1 e2 ~>* eagerlet e1' e2.
Proof.
  intro h. unfold eagerlet.
  destruct e1. 
  apply ret_steps_to_itself in h. rewrite h. eapply ms_refl.
  all: destruct e1'.
  all: try solve [eapply ms_let_cong; eauto].
  all: eapply ms_app; [ eapply ms_let_cong; eauto |
                        eapply ms_one; econstructor ].
Qed.  


(* ------------------ Application -----------------  *)

(** We define "app e1 e2" using eagerlet. Because of 
    the nested lets, we need to weaken e2 in the 
    definition. *)
Definition app_tm {n} (e1 e2 : Tm n) : Tm n := 
  eagerlet e1 (eagerlet e2⟨↑⟩ (app (var f1) (var f0))).

Lemma app_subst {n m} (e1 e2 : Tm n) (σ : fin n -> Val m) : 
  (app_tm e1 e2)[σ] = app_tm e1[σ] e2[σ].
Proof.
  unfold app_tm.
  repeat rewrite eagerlet_subst.
  repeat f_equal.
  asimpl. done.
Qed.

Lemma t_app_tm {n} Γ (e1 e2: Tm n) τ1 τ2 : 
    Γ |-e e1 ∈ (Arr τ1 τ2) -> Γ |-e  e2 ∈ τ1 ->
    Γ |-e (app_tm e1 e2) ∈ τ2.
Proof. 
  intros. unfold app_tm.
  eapply t_eagerlet; eauto with renaming rec.
  eapply t_eagerlet; eauto with renaming rec.
  repeat (econstructor; eauto with renaming rec).
Qed.


Lemma s_app_tm_cong1 (e1 e1' e2 : Tm 0) :
  e1 ~>* e1' -> app_tm e1 e2 ~>* app_tm e1' e2.
Proof. intro h. 
       unfold app_tm. 
       eapply ms_eagerlet_cong; auto. 
Qed.


Lemma s_app_tm_cong2 v1 (e2 e2' : Tm 0) :
  e2 ~>* e2' -> app_tm (ret v1) e2 ~>* app_tm (ret v1) e2'.
Proof. 
  intro h.
  unfold app_tm. 
  repeat rewrite eagerlet_retv.
  repeat rewrite eagerlet_subst.
  eapply ms_eagerlet_cong.
  asimpl.
  auto.
Qed.

(* ------------------ Succ -----------------  *)

(** Because the successor term has only a single subterm, 
    we don't need to use eager let. *)
Definition succ_tm {n} (e : Tm n) := 
  let_ e (ret (succ (var f0))).

Lemma succ_subst {n m} (e : Tm n) (σ : fin n -> Val m) : 
  (succ_tm e)[σ] = succ_tm e[σ].
Proof.
  unfold succ_tm.
  cbn.
  f_equal.
Qed.

Lemma t_succ_tm {n} Γ (e : Tm n) :
    Γ |-e e ∈ Nat -> 
    Γ |-e succ_tm e ∈ Nat.
Proof.
  intros h.
  unfold succ_tm.
  repeat (econstructor; eauto with rec).
Qed.

Lemma s_succ_tm_lit (v : Val 0) :
  succ_tm (ret v) ~> ret (succ v).
Proof.
  unfold succ_tm.
  eauto with rec.
Qed.

Lemma s_succ_cong (e1 e1' : Tm 0) : 
  e1 ~> e1' -> 
  succ_tm e1 ~> succ_tm e1'.
Proof.
  intros h.
  unfold succ_tm.
  eauto with rec.
Qed.

(* ----------------- ifz --------------------- *)

Definition ifz_tm {n} (e : Tm n) (e0 : Tm n) (e1 : Tm (S n)) := 
  let_ e (ifz (var f0) e0⟨↑⟩ e1⟨up_ren ↑⟩).

Lemma ifz_subst {n m} (e : Tm n) e0 e1 (σ : fin n -> Val m) : 
  (ifz_tm e e0 e1)[σ] = ifz_tm e[σ] e0[σ] e1[⇑σ].
Proof.
  unfold ifz_tm.
  cbn.
  repeat f_equal.
  asimpl. done.
  asimpl. done.
Qed.

Lemma t_ifz_tm {n} Γ (e : Tm n) (e0 : Tm n) (e1 : Tm (S n)) (τ : Ty 0) :
  Γ |-e e ∈ Nat -> Γ |-e e0 ∈ τ -> Nat .: Γ |-e e1 ∈ τ -> Γ |-e ifz_tm e e0 e1 ∈ τ.
Proof. 
  intros h h0 h1.
  unfold ifz_tm.
  repeat (econstructor; eauto with rec renaming).
Qed.

Lemma t_ifz_cong (e e' : Tm 0) e0 e1 : 
  e ~> e' -> 
  ifz_tm e e0 e1 ~> ifz_tm e' e0 e1.
Proof.
  intro h.
  unfold ifz_tm.
  eauto with rec.
Qed.

(* ----------------- Products ---------------------- *)


