Require Export common.core.
Require Export rec.typing.

Import rec.typing.Notations.

(** Where does the Semantic Soundness proof fall short *)

Fixpoint V (τ : Ty 0) {struct τ} : Val 0 -> Prop := 
  match τ with 
  | Void => fun v => False
  | Nat => fun v => exists k, v = lit k
  | Arr τ1 τ2 => 
      fun v => 
        forall w, V τ1 w -> exists w', app v w ~>* ret w' /\ V τ2 w' 
        (* NOTE: compare to this version, which doesn't include rec
           exists e, v = abs e /\
            forall w, V τ1 w -> exists w', e[w..] ~>* ret w' /\ V τ2 w' 
         *)


  | Prod τ1 τ2 => 
      fun v => 
        (exists v1, prj1 v ~>* ret v1 /\ V τ1 v1) /\
        (exists v2, prj2 v ~>* ret v2 /\ V τ2 v2)
        (* NOTE: compare to this version
           exists v1 v2, v = prod v1 v2 /\ V τ1 v1 /\ V τ2 v2
        *)

  | Sum τ1 τ2 => 
      fun v => (exists v1, v = inj true v1 /\ V τ1 v1) \/
            (exists v2, v = inj false v2 /\ V τ2 v2)
      (* NOTE: is there a version with case? *)
(*
  (* NOTE: THIS IS NOT WELL FOUNDED *)
  | Mu τ => 
      fun v => 
        exists w, v = fold w /\ V (τ [(Mu τ)..]) w 
*)
  | _ => fun v => False
  end.

Definition C (τ : Ty 0) : Tm 0 -> Prop := 
  fun e =>  exists v, e ~>* ret v /\ V τ v.

Lemma reverse_evaluation e e' τ :
  e ~> e' -> C τ e' -> C τ e.
Proof. 
  intros h [v [S Vv]]. 
  exists v. split. eapply ms_trans; eauto. auto.
Qed.

Definition Env n := fin n -> Val 0.

Definition semantic_subst {n} (Γ : Ctx n) (ρ : Env n) := 
  forall x, V (Γ x) (ρ x).

Definition semantic_typing {n} (Γ : Ctx n) e τ :=
  forall ρ, semantic_subst Γ ρ -> C τ e[ρ].

Module SoundnessNotation.
Notation "V⟦ τ ⟧" := (V τ).
Notation "C⟦ τ ⟧" := (C τ).
Notation "⟦ Γ ⟧" := (semantic_subst Γ). 
Notation "Γ ⊨v v ∈ τ" := (forall ρ, ⟦ Γ ⟧ ρ -> V τ v[ρ]) (at level 70).
Notation "Γ ⊨ e ∈ τ" := (forall ρ, ⟦ Γ ⟧ ρ -> C τ e[ρ]) (at level 70).
End SoundnessNotation.

Import SoundnessNotation.

Lemma semantic_subst_cons {τ v} {n} {Γ : Ctx n} {ρ} : 
  V⟦ τ ⟧ v ->  ⟦ Γ ⟧ ρ ->   ⟦ τ .: Γ ⟧ (v .: ρ).
Proof. unfold semantic_subst. intros Vv h. auto_case. Qed.


(* Semantic typing rules *)

Lemma semantic_var {n} (Γ : Ctx n) x : 
  Γ ⊨v var x ∈ Γ x.
Proof. 
  intros ρ ρH.
  specialize (ρH x). 
  asimpl.
  eauto.
Qed.

Lemma semantic_abs {n} (Γ : Ctx n) (e : Tm (S n)) τ1 τ2 : 
  (τ1 .: Γ) ⊨ e ∈ τ2 -> 
  Γ ⊨v (abs e) ∈ Arr τ1 τ2.
Proof.
  intros IH.
  intros ρ ρH.
  cbn.
  intros w wIn.
  move: (IH (w .: ρ)) => CH. 
  eapply reverse_evaluation.
  eapply Small.s_beta.
  asimpl.
  eapply CH. eapply semantic_subst_cons; eauto.
Qed.

Lemma semantic_app {n} (Γ : Ctx n) v1 v2 τ1 τ2 : 
  Γ ⊨v v1 ∈ Arr τ1 τ2 -> 
  Γ ⊨v v2 ∈ τ1 -> 
  Γ ⊨ app v1 v2 ∈ τ2.
Proof.
  intros h1 h2 ρ ρh.
  specialize (h1 ρ ρh). 
  specialize (h2 ρ ρh). 
  cbn in h1.
  cbn.
  eapply h1; eauto.
Qed.


Lemma semantic_lit {n} {Γ : Ctx n} {k:nat} :
   Γ ⊨v lit k ∈ Nat.
Proof.
  intros ρ ρH.
  cbn. 
  eauto.
Qed.

Lemma semantic_succ {n} {Γ : Ctx n} {v:Val n} :
  Γ ⊨v v ∈ Nat ->
  Γ ⊨ succ v ∈ Nat.
Proof.
(* FILL IN HERE *) Admitted.

Lemma semantic_ifz {n} {Γ : Ctx n} v {e0:Tm n}{e1: Tm (S n)}{τ}  : 
  Γ ⊨v v ∈ Nat -> 
  Γ ⊨ e0 ∈ τ -> 
  Nat .: Γ ⊨ e1 ∈ τ -> 
  Γ ⊨ ifz v e0 e1 ∈ τ.
Proof.
(* FILL IN HERE *) Admitted.


(** Now let's try to repeat the argument for rec. *)
Lemma semantic_rec {n} (Γ : Ctx n) (v : Val (S n)) τ1 τ2 : 
  Arr τ1 τ2 .: Γ ⊨v v ∈ (Arr τ1 τ2) -> 
  Γ ⊨v (rec v) ∈ Arr τ1 τ2.
Proof.
  intros IH. intros ρ ρH.
  (* OUR Goal:  V⟦ Arr τ1 τ2 ⟧ (rec v)[ρ] *)
  cbn.
  intros w wIn.
  eapply reverse_evaluation.
  eapply Small.s_app_rec.
  specialize (IH ((rec v)[ρ] .: ρ)).
  asimpl.
  eapply IH; auto.
  eapply semantic_subst_cons; auto.
  (* BUT: this is what we are trying to prove!!! *)
Abort.

