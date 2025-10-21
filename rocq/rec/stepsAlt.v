(** This file demonstrates the definition of a step-indexed logical 
    relation using structural recursion over natural number steps.
    It does not require well-founded recursion or strong induction.

*)

(* For reasoning about numbers *)
From Stdlib Require Import Arith.
From Stdlib Require Import Psatz.

Require Export common.core.

Require Export rec.typing.
Import reduction.Notations.

Require Import rec.iprop.
Import iprop.Notations.

(** The computation relation is the same as before. *)

Fixpoint C' (V : Val 0 -> iProp) (e : Tm 0) (k : nat) {struct k} : Prop := 
  (irreducible e -> exists v, e = ret v /\ V v k) /\ 
      (forall e', e ~> e' -> ▷ (C' V e') k).
                      
(** This version of the value relation is defined by structural induction on
   [k]. The key idea is to work downward closure *directly* into the abs
   case. 
*)
Fixpoint V (t : Ty 0) (v : Val 0) k {struct k} := 
  match t with 
    | Void => False 

    | Nat => is_nat v = true

    | Arr t1 t2 => 
       (exists v2, v = rec v2 /\ ▷ (V (Arr t1 t2) (v2[v..])) k ) \/
       (exists e,  v = abs e /\ ▷ (V (Arr t1 t2) v) k /\
         forall v1, ▷ (V t1 v1) k -> ▷ (C' (V t2) e[v1..]) k)

    | Prod t1 t2 => 
      (exists v2, v = rec v2 /\ ▷ (V (Prod t1 t2) (v2[v..])) k) \/
      (exists v1 v2, v = prod v1 v2 /\ ▷ (V t1 v1) k  /\ ▷ (V t2 v2) k)

    | Sum τ1 τ2 => 
         (exists v1, v = inj true v1 /\ ▷ (V τ1 v1) k) \/
         (exists v2, v = inj false v2 /\ ▷ (V τ2 v2) k)

    | Mu τ => 
         (exists v2, v = fold v2 /\
             ▷  (V (τ [(Mu τ)..]) v2) k)
    | _ => False
end.


Definition C τ e k := C' (V τ) e k.

(** * Convenience lemmas for unfolding the definitions of C and V *)

Lemma C_def : forall τ e k,
  C τ e k = ((irreducible e -> exists v, (e = ret v /\ V τ v k)) /\ 
             (forall e', e ~> e' -> ▷ (C τ e') k)).
Proof.
  intros. destruct k. cbn. done.
  unfold C. unfold C'. done.
Qed.

Lemma V_Nat v k :
  V Nat v k <-> is_nat v = true.
Proof. destruct k; cbn; tauto. Qed.

Lemma V_Arr_rec t1 t2 v k :  
  V (Arr t1 t2) (rec v) k <->
        ▷ (V (Arr t1 t2) (v[(rec v)..])) k.
Proof. 
  destruct k; cbn.
  - split; eauto.
  - split.
    intros [[? [EQ ?]]|[? [EQ h1]]]; inversion EQ.
    subst; done.
    intros h. left. exists v. split; eauto.
Qed.

Lemma V_Arr_abs t1 t2 e k : 
  V (Arr t1 t2) (abs e) k <->
       (▷ (V (Arr t1 t2) (abs e)) k /\
         forall v1, ▷ (V t1 v1) k -> ▷ (C' (V t2) e[v1..]) k).
Proof.
  destruct k; cbn.
  - split; eauto.
  - split.
    intros [[? [h1 ?]]|[? [EQ h1]]]. done.
    inversion EQ; subst. done.
    intros [h1 h2].
    right. exists e. split; auto.
Qed.

(** * Proof that the logical relation is downward closed *)

Instance IProp_C' {V : Val 0 -> iProp} `{forall v, IProp (V v)} {e} : IProp (C' V e).
Proof.
split. move=>k. move: e. induction k; intros e.
- cbn. intros [h1 h2]. intros j LE. inversion LE. cbn. done.
- unfold C'. fold C'. intros [h1 h2]. intros j LE. inversion LE; subst.
  + split. eapply h1. auto.
  + cbn in h2. 
    eapply IHk; eauto.
    destruct k. 
    * unfold C'. fold C'. 
      split. intro ie. move: (h1 ie) => [v [EQ h1']]. clear h1. subst.
      exists v. split; auto.  eapply H; eauto.
      cbn. auto.
    * unfold C'. fold C'.
      split.
      intro h. destruct h1 as [v1 [EQ VV]]; auto.
      exists v1. split; auto. eapply H; eauto. 
      intros e' SS. specialize (h2 _ SS).  cbn.
      eapply IHk; eauto.
Qed.    

Instance IProp_V {τ v} : IProp (V τ v). 
Proof.
constructor.
intro k.  move: τ v.
induction k.
- intros τ v V0 j LEj. inversion LEj. done.
- intros τ v Vsk j LEj. inversion LEj.
  + subst. done.
  + subst.
    destruct τ.
    all : cbn in Vsk.
    * done.
    * done.
    * destruct j. cbn. done. cbn. done.
    * destruct Vsk as [h|h].
      destruct h as [v2 [EQ h]]. 
      cbn in h. destruct j. cbn. left; eauto.
      cbn. left. exists v2. split; eauto.  eapply IHk. auto. lia.
      destruct h as [v1 [v2 [EQ h]]].
      cbn in h. destruct h as [h1 h2].
      destruct j. cbn. right. eauto.
      right. exists v1. exists v2. split; eauto. split; eauto.
      eapply IHk; eauto. lia. eapply IHk; eauto. lia.
    * destruct Vsk as [[v1 [EQ V1]]|[v2 [EQ V2]]].
      destruct j.
      cbn. eauto. cbn. left. exists v1. split; eauto.
      eapply IHk; eauto. lia.
      destruct j.
      cbn. eauto. cbn. right. exists v2. split; eauto.
      eapply IHk; eauto. lia.
    * destruct Vsk as [h|h].
      destruct h as [v2 [EQ h]].
      cbn in h. destruct j. cbn. left. eauto.
      cbn. left. exists v2. split; eauto. 
      eapply IHk; eauto. lia.
      destruct h as [e [EQ [h1 h2]]].
      cbn in h1. eapply IHk; eauto.
    * destruct Vsk as [v2 [EQ h]]. cbn in h.
      destruct j; cbn.
      eexists; split; eauto.
      eexists; split; eauto.
      eapply IHk; eauto. lia.
Qed.

Instance IProp_C {τ} {e} : IProp (C τ e).
Proof.
  unfold C. constructor.
  eapply dclosed.
Qed.

(** * Step-indexed Semantic typing relations *)

(* We want the semantic relations to also be downward closed. For that 
   reason, we define semantic_typing and semantic_typing_val using the 
   ⇒ operation from rec.iprop. *)

Definition Env n := fin n -> Val 0.

Definition semantic_subst {n} Γ (ρ : Env n) k := 
  forall (i : fin n), (V (Γ i) (ρ i) k).

Definition semantic_typing {n} (Γ : Ctx n) e τ k :=
  forall ρ, (semantic_subst Γ ρ ⇒ C τ (e [ρ])) k.

Definition semantic_typing_val {n} (Γ : Ctx n) v τ k :=
  forall ρ, (semantic_subst Γ ρ ⇒ V τ (v [ρ])) k.


Module SoundnessNotation.
Notation "⟦ Γ ⟧" := (semantic_subst Γ). 
Notation "Γ ⊨v v ∈ τ @ k" := (semantic_typing_val Γ v τ k) (at level 20).
Notation "Γ ⊨ e ∈ τ @ k" := (semantic_typing Γ e τ k) (at level 20).
End SoundnessNotation.

Import SoundnessNotation.

Lemma semantic_subst_cons {τ v} {n} {Γ : Ctx n} {ρ} {k} :
  V τ v k ->  ⟦ Γ ⟧ ρ k ->  ⟦ τ .: Γ ⟧ (v .: ρ) k.
Proof. intros. unfold semantic_subst in *. auto_case. Qed.

#[export] Instance dclosed_semantic_subst {n} (ρ : Env n) Γ : 
  IProp (⟦ Γ ⟧ ρ). 
Proof. constructor. intros i h j LE x. eapply dclosed; eauto. Qed.
#[export]  Instance dclosed_semantic_typing {n} (Γ : Ctx n) e τ : 
  IProp (semantic_typing Γ e τ). 
Proof. constructor. intros. intros ρ. eapply dclosed; eauto. Qed.
#[export]  Instance dclosed_semantic_typing_val {n} (Γ : Ctx n) v τ : 
  IProp (semantic_typing_val Γ v τ ). 
Proof. constructor. intros. intros ρ. eapply dclosed; eauto. Qed.


(** * Semantic typing rules *)

Section Semtyping.
Context {n : nat} (Γ : Ctx n).


Lemma ST_var x k :
  (* ------------------------ *)
  Γ ⊨v var x ∈ (Γ x) @ k.
Proof.
  intros ρ i LE hρ.
  asimpl. 
  unfold semantic_subst in hρ. 
  eauto.
Qed. 


Lemma ST_zero k :
 (* ------------------- *)
  Γ ⊨v zero ∈ Nat @ k.
Proof.
  intros ρ j LE h. cbn.
  rewrite V_Nat. 
  auto.
Qed.

Lemma ST_succ v k :
  Γ ⊨v v ∈ Nat @ k ->
 (* ------------------- *)
  Γ ⊨v succ v ∈ Nat @ k.
Proof.
(* FILL IN HERE *) Admitted.


(** Key helper lemma for the application case, proven by structural induction on k. *)
Lemma C_app k : forall τ1 τ2 (v1 v2 : Val 0), 
  V (Arr τ1 τ2) v1 k -> 
  V τ1 v2 k -> 
  C τ2 (app v1 v2) k.
Proof.
  intros τ1 τ2.
  induction k.
  all: intros v1 v2.
  all: intros h hV. 
  all: rewrite C_def.
  - (* k=0 *) split.
    + (* Observe that in this case, we need V τ v 0 to give us something 
         like canonical forms so that we can say that the application always reduces. *)
      destruct h as [[v [h1 _]]|[e [h1 _]]]; subst; is_reducible.
    + done. 
  - (* k=S k *)
    (* For both the rec and abs cases, need to lower the assumption about the 
       argument v2 *)
    apply dclosed with (j := k) in hV; auto.
    destruct h as [[v [EQ ?]]|[e [EQ [? h1]]]]; subst.
    all: split; try is_reducible.
    + (* v1 = rec v *)
      intros e' APP. 
      inversion APP; subst.
      eapply IHk; eauto.  
    + (* v1 = abs e *) 
      intros e' APP. 
      inversion APP; subst.
      eapply h1; eauto.  
Qed.

Lemma ST_app v1 v2 A B k :
    Γ ⊨v v1 ∈ (Arr A B) @ k ->
    Γ ⊨v v2  ∈ A         @ k ->
    (* --------------- *)
    Γ ⊨ (app v1 v2) ∈ B @ k.
Proof.
  intros h1 h2.
  intros ρ j LE Hρ. cbn.
  eapply C_app; eauto. eapply h1; eauto. eapply h2; eauto.
Qed.


Lemma ST_abs τ1 τ2 e k : 
  (τ1 .: Γ) ⊨ e  ∈ τ2 @ k ->
  (* --------------------------------- *)
  Γ ⊨v abs e ∈ (Arr τ1 τ2) @ k.
Proof.
  intros SV ρ j LE hρ.
  have: (forall v, (V τ1 v ⇒ C τ2 (e [v .: ρ])) j).
  { intros v i pf hV. eapply SV. lia. 
    eapply semantic_subst_cons; eauto. eapply dclosed; eauto. } 
  clear k LE SV hρ.
  cbn.
  induction j; intros h; rewrite V_Arr_abs.
  - done.
  - cbn.
    split.
    * eapply IHj. 
      intros v i LEi hv.
      eapply h; eauto.
    * intros v hV.
      asimpl.
      eapply h; eauto.
Qed.


Lemma ST_rec_Arr τ1 τ2 v k : 
  (Arr τ1 τ2 .: Γ) ⊨v v ∈ Arr τ1 τ2 @ k ->
  (* --------------------------------- *)
  Γ ⊨v rec v ∈ (Arr τ1 τ2) @ k.
Proof.
  intros SV ρ j LE hρ.
  have: (forall v1, (V (Arr τ1 τ2) v1 ⇒ V (Arr τ1 τ2) v[v1 .: ρ]) j).
  { intros v1 i pf hV. eapply SV. lia. 
    eapply semantic_subst_cons; eauto. eapply dclosed; eauto. } 
  clear k LE SV hρ.
  cbn.
  induction j; intros h.
  - rewrite V_Arr_rec. cbn. done.
  - have h1: V (Arr τ1 τ2) (rec v[⇑ ρ]) j.
    eapply IHj. intros v1 i LEi V1. eapply h; eauto.
    rewrite V_Arr_rec. cbn.
    asimpl.
    eapply h. lia.
    eapply h1.
Qed.

Lemma ST_ret v τ k : 
  Γ ⊨v v ∈ τ @ k -> 
  (* ------------------------ *)
  Γ ⊨ (ret v) ∈ τ @ k.
Proof.
  intros h ρ i LE hρ.
  asimpl.
  rewrite C_def; eauto.
  split. intros. eexists; split; eauto.
  eapply h; eauto.
  intros e' SS. inversion SS.
Qed.



Lemma ST_let e1 e2 τ1 τ2 k : 
 Γ ⊨ e1 ∈ τ1 @ k -> 
 (τ1 .: Γ) ⊨ e2 ∈ τ2 @ k -> 
 Γ ⊨ let_ e1 e2 ∈ τ2 @ k.
Proof.
(* FILL IN HERE *) Admitted.

End Semtyping.
