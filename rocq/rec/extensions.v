Require Export rec.typing.

Import typing.Notations.
Import reduction.Notations.

(** Syntax extensions *)

(** We can define abbreviations for "normal" lambda calculus terms, 
    which do not include value restrictions, by using eagerlet *)

Import FinValues.

(** eager let *) 

Definition eagerlet {n} (e1 : Tm n) (e2 : Tm (S n)) :=
  match e1 with 
  | ret v => e2[v..]
  | _ => let_ e1 e2
  end.

Lemma t_eagerlet {n} Γ :
  forall (e1 : Tm n) (e2 : Tm (S n)) (τ1 τ2 : Ty 0), 
    Γ |-e e1 ∈ τ1 -> τ1 .: Γ |-e e2 ∈ τ2 -> Γ |-e eagerlet e1 e2 ∈ τ2.
Proof. 
  intros. unfold eagerlet.
  unfold eagerlet. intros. destruct e1; eauto. inversion H.
  eapply substitution_tm; eauto with rec.
  all: eauto with rec.
Qed.

Lemma eagerlet_subst {m n : nat} (sigma : fin n -> Val m) (e1 : Tm n) (e2 : Tm (S n)) :
   (eagerlet e1 e2)[sigma] = eagerlet (e1[sigma]) (e2[up_Val_Val sigma]).
Proof. 
  destruct e1; cbn; try reflexivity. now asimpl.
Qed.

Lemma ms_eagerlet_cong (e1 e1' : Tm 0) (e2 : Tm 1) :
  e1 ~>* e1' -> eagerlet e1 e2 ~>* eagerlet e1' e2.
Proof.
  intro h. unfold eagerlet.
  destruct e1. apply ret_steps_to_itself in h. rewrite h. eapply ms_refl.
  all: destruct e1'.
  all: try solve [eapply ms_let_cong; eauto].
  all: eapply ms_app; [ eapply ms_let_cong; eauto| eapply ms_one; econstructor ].
Qed.  


(* ------------------ Application -----------------  *)

Definition app_tm {n} (e1 e2 : Tm n) : Tm n := 
  eagerlet e1 (eagerlet e2⟨↑⟩ (app (var f1) (var f0))).


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
Proof. intro h.  unfold app_tm. eapply ms_eagerlet_cong; auto. 
Qed.


Lemma s_app_tm_cong2 v1 (e2 e2' : Tm 0) :
  e2 ~>* e2' -> app_tm (ret v1) e2 ~>* app_tm (ret v1) e2'.
Proof. 
  intro h.
  unfold app_tm. 
  asimpl.
  unfold eagerlet at 1 3.
  repeat rewrite eagerlet_subst.
  eapply ms_eagerlet_cong.
  asimpl.
  auto.
Qed.


(* ----------------- Products ---------------------- *)

Definition prod_tm {n} (e1 e2 : Tm n) : Tm n := 
  eagerlet e1 (eagerlet e2⟨↑⟩ (ret (prod (var f1) (var f0)))).
Definition prj_tm {n} b (e1 : Tm n) : Tm n := 
  eagerlet e1 (prj b (var f0)).

(** Typing rules for extended product syntax *)

Definition t_prod_tm {n} (Γ : Ctx n) e1 e2 τ1 τ2 : 
    Γ |-e e1 ∈ τ1 ->   Γ |-e e2 ∈ τ2 -> 
    Γ |-e prod_tm e1 e2 ∈ Prod τ1 τ2.
Proof.
  intros. unfold prod_tm.
  eapply t_eagerlet; eauto with renaming rec.
  eapply t_eagerlet; eauto with renaming rec.
Qed.

Definition s_prod_cong1 e1 e1' e2 :
  e1 ~>* e1' ->
  prod_tm e1 e2 ~>* prod_tm e1' e2.
Proof.
  intro h.
  unfold prod_tm.
  eapply ms_eagerlet_cong; eauto.
Qed.

Definition s_prod_cong2 v1 e2 e2' :
  e2 ~>* e2' ->
  prod_tm (ret v1) e2 ~>* prod_tm (ret v1) e2'.
Proof.
  intro h.
  unfold prod_tm.
  unfold eagerlet at 1 3.
  repeat rewrite eagerlet_subst.
  eapply ms_eagerlet_cong.
  asimpl.
  done.
Qed.

Lemma t_prj1_tm {n} Γ (e:Tm n) τ1 τ2 : 
  Γ |-e e ∈  Prod τ1 τ2 -> 
  Γ |-e prj_tm true e ∈ τ1.
Proof.
  intros h. unfold prj_tm.
  eapply t_eagerlet; eauto with renaming rec.
  econstructor; eauto with rec.
  eapply t_var'. cbn. eauto.  
Qed.


Lemma t_prj2_tm {n} Γ (e:Tm n) τ1 τ2 : 
  Γ |-e e ∈  Prod τ1 τ2 -> 
  Γ |-e prj_tm false e ∈ τ2.
Proof.
  intros h. unfold prj_tm.
  eapply t_eagerlet; eauto with renaming rec.
  econstructor; eauto with rec.
  eapply t_var'. cbn. eauto.  
Qed.


Definition s_prj_cong b e1 e1' :
  e1 ~>* e1' ->
  prj_tm b e1 ~>* prj_tm b e1'.
Proof.
  intro h.
  unfold prj_tm.
  eapply ms_eagerlet_cong; eauto.
Qed.





