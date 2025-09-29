(** This file demonstrates a semantic soundness proof using a step-indexed logical 
    relation. The main result of this file (type safety) is underwhelming, as we 
    could already prove it more straightforwardly using preservation and progress. 

    However, this proof is meant to be a template for more powerful results that 
    are later to come. For that reason, we make sure that the language that we 
    consider stresses the proof technique by including both recursive values and 
    iso-recursive types.

    Further reading: Some of the definitions in this development are inspired by 
    Lectures given by Xavier Leroy, titled "Programming = proving?
    The Curry-Howard correspondence today" 
    https://xavierleroy.org/CdF/2018-2019/8.pdf

    Additional reading about the foundations of induction and coinduction is available
    in the execellent lecture notes by Ron Garcia:
    https://www.cs.ubc.ca/~rxg/cpsc509-spring-2022/06-coinduction.pdf

*)

From Stdlib Require Import Psatz.
From Stdlib Require Import Arith.

Require Export common.core.
Require Export rec.typing.
Import reduction.Notations.

(** ----------------------------------------------- *)
(** Step-indexed propositions                       *)

(* See iprop. *)

Require Export rec.iprop.
Import iprop.Notations.


Section Safety.

(* Recall our step-indexed version of type safety: a program is **safe for n
   steps** if it doesn't get stuck within n steps of execution. Let P_i be the
   set of all terms that are safe for i steps. That gives us a sequence of
   sets, where P_0 contains all programs,, which is a superset of P_1, which
   includes all programs except those that are immediately stuck, etc.

      P_0 ⊇ P_1 ⊇ P_2 ⊇ P_3 ⊇ P_4 ⊇ P_5 ....

   The limit of this sequence (⋂_i P_i) is the set of all safe programs, those
   that never get stuck after any finite number of steps.  Type safety then
   means that we prove that well-typed programs are in every set P_i, for any
   i. 

*)

Local Definition next ϕ := (fun k => match k with O => True | S j => ϕ j end).

(** One way we can write this proposition is like this: *)
Fixpoint P e k := 
  (irreducible e -> exists v, e = ret v) /\ (forall e', e ~> e' -> next (P e') k).

Lemma P_def e k : 
  P e k = ((irreducible e -> exists v, e = ret v) /\ (forall e', e ~> e' -> next (P e') k)).
Proof. destruct k; cbn; reflexivity. Qed.


(** This definition lines up with a more usual definition of type safety *)
Lemma P_safety e : 
  (forall k, P e k) -> forall e', e ~>* e' -> irreducible e' -> exists v : Val 0, e' = ret v.    
Proof.
  intros h e' RED.
  induction RED.
  - intros. specialize (h 0). cbn in h. destruct h. eauto.
  - eapply IHRED.
    intros k.  destruct (h (S k)) as [h1 h2]. eapply h2; eauto.
Qed.

Lemma safety e τ : typing null e τ -> forall k, P e k.
Proof.
intros h k. move: e h.
eapply strong_ind with (P := fun k => forall e : Tm 0, typing null e τ -> P e k).
clear k. intros k ih.
intros e h. rewrite P_def. 
split.
- destruct (progress _ _ h).
  + intros _. auto.
  + is_reducible.
- intros e' SS. destruct k; try done. cbn.
  eapply ih. auto.
  eapply preservation; eauto.
Qed.


End Safety.


(** --------------------------------------------------- *)
(** Axiomatization of the step-indexed logical relation *)

Module Type LogicalRelation.

Axiom V : Ty 0 -> Val 0 -> nat -> Prop.
Axiom C : Ty 0 -> Tm  0 -> nat -> Prop.

Axiom C_def : forall τ e k,
  C τ e k = ((irreducible e -> exists v, (e = ret v /\ V τ v k)) /\ 
             (forall e', e ~> e' -> ▷ (C τ e') k)).

Axiom V_Void : forall v k, V Void v k = False  .
Axiom V_Nat  : forall v k, V Nat v k = exists n,  v = lit n.
Axiom V_Arr  : forall τ1 τ2 v k, 
    V (Arr τ1 τ2) v k = 
         ((exists v2, v = rec v2 /\ 
             (▷ (V (Arr τ1 τ2) (v2[v..])) k)) \/ 
         (exists e,  v = abs e  /\ 
             (forall v1, (▷ (V τ1 v1) ⇒ ▷ (C τ2 e[v1..])) k))).
Axiom V_Prod : forall τ1 τ2 v k, 
    V (Prod τ1 τ2) v k = 
         ((exists v2, v = rec v2 /\ 
             (▷ (V (Prod τ1 τ2) (v2[v..]))) k) \/ 
         (exists v1 v2,  v = prod v1 v2  /\ 
              ▷ (V τ1 v1) k /\ ▷ (V τ2 v2) k)).
Axiom V_Sum : forall τ1 τ2 v k, 
    V (Sum τ1 τ2) v k = 
         ((exists v1, v = inj true v1 /\ ▷ (V τ1 v1) k) \/
         (exists v2, v = inj false v2 /\ ▷ (V τ2 v2) k)).

Axiom V_Mu : forall τ v k,
    V (Mu τ) v k = (exists v2, v = fold v2 /\
                            (▷ (V (τ [(Mu τ)..]) v2)) k).  
End LogicalRelation.

Module Core (LR : LogicalRelation).

Import LR.
Create HintDb LR. 

#[export] Hint Rewrite C_def V_Void V_Nat V_Arr V_Prod V_Sum V_Mu : LR.
Ltac lrsimpl := autorewrite with LR.

(* Proof that C implies type safety *)
Lemma C_safety e tau : 
  (forall k, C tau e k) -> 
  forall e', e ~>* e' -> irreducible e' -> exists v : Val 0, e' = ret v.    
Proof. 
 intros h e' RED.
 induction RED.
  - intros. specialize (h 0). rewrite C_def in h. destruct h.
    destruct (H0 H) as [v [EQ VV]]. eauto.
  - eapply IHRED.
    intros k. 
    specialize (h (S k)). 
    rewrite C_def in h. 
    destruct h as [_ h2]. 
    specialize (h2 _ H). cbn in h2.
    auto.
Qed.

Definition Env n := fin n -> Val 0.

Definition semantic_subst {n} Γ (ρ : Env n) k := 
  forall (i : fin n), (V (Γ i) (ρ i) k).

Definition semantic_typing {n} (Γ : Ctx n) e τ k :=
  forall ρ, (semantic_subst Γ ρ ⇒ C τ (e [ρ])) k.

Definition semantic_typing_val {n} (Γ : Ctx n) v τ k :=
  forall ρ, (semantic_subst Γ ρ ⇒ V τ (v [ρ])) k.


Module SoundnessNotation.
Notation "⟦ Γ ⟧" := (semantic_subst Γ). 
Notation "Γ ⊨v v ∈ τ @" := (semantic_typing_val Γ v τ) (at level 20).
Notation "Γ ⊨ e ∈ τ @" := (semantic_typing Γ e τ) (at level 20).
End SoundnessNotation.

Import SoundnessNotation.

Lemma semantic_subst_cons {τ v} {n} {Γ : Ctx n} {ρ} {k} :
  V τ v k ->  ⟦ Γ ⟧ ρ k ->  ⟦ τ .: Γ ⟧ (v .: ρ) k.
Proof. intros. unfold semantic_subst in *. auto_case. Qed.

(** --------------------------------------------------- *)
(** Proof that the Logical relation is downward closed  *)

Ltac prep_ih j LE := 
  inversion LE; subst;[done| destruct j;[ done| cbn in *]].

#[export] Instance dclosed_V {τ}{v : Val 0} : IProp (V τ v).
split. move=> k. move: τ v.
eapply strong_ind with (P := fun k =>
  forall τ v, V τ v k -> forall j : nat, j <= k -> V τ v j).
clear k. intros k ih.
intros t v.
intros Vk j LE.
destruct t; autorewrite with LR in Vk; autorewrite with LR.
- destruct f.
- done.
- done.
- destruct Vk as [[v2 [EQ h]]|[v1 [v2 [EQ [h1 h2]]]]].
  left. exists v2. split. auto.
  prep_ih j LE. eapply (ih m); eauto. lia.
  right. exists v1, v2. split. auto. 
  prep_ih j LE. split; eapply (ih m); eauto; lia.
- destruct Vk as [[v1 [EQ h]]| [v2 [EQ h]]].
  left. exists v1. split; auto. prep_ih j LE. eapply (ih m); eauto; lia.
  right. exists v2. split. auto. prep_ih j LE. eapply (ih m); eauto; lia.
- destruct Vk as [[v2 [EQ h]]|[e [EQ h]]].
  left. exists v2. split. auto.  prep_ih j LE. eapply (ih m); eauto; lia.
  right. exists e. split. auto. intros v1. 
  intros i LEi. eapply h. lia.
- destruct Vk as [v2 [EQ h]].
  exists v2. split; auto. prep_ih j LE. eapply (ih m); eauto; lia.
Qed.

#[export] Instance dclosed_C τ (e : Tm 0) : IProp (C τ e).
split. move=>k. move: e. induction k; intros e.
- rewrite C_def. intros [h1 h2]. intros j LE. inversion LE. rewrite C_def.    
  subst. split. auto. auto.
- rewrite C_def. intros [h1 h2]. intros j LE. inversion LE; subst.
  + rewrite C_def. split. eapply h1. auto.
  + eapply IHk; eauto.
    rewrite C_def. split.
    intro h. destruct h1 as [v1 [EQ VV]]; auto.
    exists v1. split; auto. eapply dclosed; eauto. 
    intros e' SS. specialize (h2 _ SS).
    destruct k; try done. cbn. eapply IHk; eauto.
Qed.    

#[export] Instance dclosed_semantic_subst {n} (ρ : Env n) Γ : 
  IProp (⟦ Γ ⟧ ρ). 
Proof. constructor. intros i h j LE x. eapply dclosed; eauto. Qed.
#[export]  Instance dclosed_semantic_typing {n} (Γ : Ctx n) e τ : 
  IProp (Γ ⊨ e ∈ τ @). 
Proof. constructor. intros. intros ρ. eapply dclosed; eauto. Qed.
#[export]  Instance dclosed_semantic_typing_val {n} (Γ : Ctx n) v τ : 
  IProp (Γ ⊨v v ∈ τ @). 
Proof. constructor. intros. intros ρ. eapply dclosed; eauto. Qed.


(** -------------------------------------------------------- *)


Ltac extract_value v Vv EQ := 
   match goal with 
   | [h1 : C ?τ1 ?e1 ?k, IR : irreducible ?e1 |- _ ] => 
     rewrite C_def in h1 ; move: h1 => [h1 _] ;
     move: (h1 IR) => [v [EQ Vv]] ; clear IR h1
   end.


(* The computation relation is closed under forward and 
   backward evaluation. We need to either add one or subtract 
   one to the step count in each case, but the "later" modality 
   allows us to write a version that hides that arithmetic. *)

Lemma backwards τ e k : 
  forall e', e ~> e' -> ▷ (C τ e') k -> C τ e k.
Proof.
  intros e' h h1.
  rewrite C_def. split.
  - is_reducible. 
  - intros e'' F. 
    eapply deterministic with (e2 := e') in F; subst; auto.
Qed.

Lemma forwards' τ (e e' : Tm 0) k :  
  e ~> e' -> C τ e (S k) -> C τ e' k.
Proof.
  intros h1 h2. rewrite C_def in h2.  move: h2 => [_ h2]. eapply h2. auto.
Qed.

Lemma forwards τ (e e' : Tm 0) k :  
  e ~> e' -> C τ e k -> ▷ (C τ e') k.
Proof.
  intros h1 h2. rewrite C_def in h2.  move: h2 => [_ h2]. eapply h2. auto.
Qed. 


Lemma C_val τ v k : 
  V τ v k -> C τ (ret v) k.
Proof.
  intros h.
  rewrite C_def. split.
  - intros. eauto.
  - intros e' SS. inversion SS.
Qed.

Lemma is_value_V τ (e : Tm 0) k : 
  C τ e k -> forall v, e = ret v -> V τ v k.
Proof.
  rewrite C_def.
  intros [hC _].
  intros v ->. 
  destruct hC. intros v0 h. inversion h.
  inversion H. inversion H0. subst. done.
Qed.


(** -------------------------------------------------------- *)

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

Lemma ST_lit i k :
 (* ------------------- *)
  Γ ⊨v lit i ∈ Nat @ k.
Proof.
  intros ρ j LE h. cbn.
  rewrite V_Nat.
  exists i; eauto.
Qed.

Lemma ST_abs τ1 τ2 e k : 
  (τ1 .: Γ) ⊨ e  ∈ τ2 @ k ->
  (* --------------------------------- *)
  Γ ⊨v abs e ∈ (Arr τ1 τ2) @ k.
Proof.
  intros SV ρ i LEi hρ. cbn.
  rewrite V_Arr.
  right.
  exists e[up_Val ρ]. split; auto.
  intros v1.
  asimpl.
  intros j LEj. next j.
  intros Vv1.  
  eapply SV; try lia.
  eapply semantic_subst_cons; auto.
  eapply dclosed; eauto. lia.
Qed.

Lemma ST_rec_Arr τ1 τ2 v k : 
  (Arr τ1 τ2 .: Γ) ⊨v v ∈ Arr τ1 τ2 @ k ->
  (* --------------------------------- *)
  Γ ⊨v rec v ∈ (Arr τ1 τ2) @ k.
Proof.
  move: v.
  eapply strong_ind with 
    (P := fun k => forall v : Val (S n), 
              ((Arr τ1 τ2 .: Γ) ⊨v v ∈ Arr τ1 τ2 @) k -> 
              (Γ ⊨v rec v ∈ Arr τ1 τ2 @) k).
  clear k. intros k ih.
  intros v SV ρ j LEj hρ.
  destruct j. rewrite V_Arr. cbn. left; eauto.
  cbn.
  rewrite V_Arr. left.
  eexists. split; eauto.
  cbn.
  asimpl. eapply SV. lia.
  eapply semantic_subst_cons; eauto.
  eapply ih; eauto. eapply dclosed; eauto. lia.
  eapply dclosed; eauto. eapply dclosed; eauto.
Qed.

Lemma C_app k : forall τ1 τ2 (v1 v2 : Val 0), 
  V (Arr τ1 τ2) v1 k -> 
  V τ1 v2 k -> 
  C τ2 (app v1 v2) k.
Proof.
  intros τ1 τ2.
  eapply strong_ind with 
    (P := fun k => 
            forall v1 v2 : Val 0, V (Arr τ1 τ2) v1 k -> V τ1 v2 k -> 
                             C τ2 (app v1 v2) k).
  clear k. intros k ih.
  intros v1 v2 h1 h2. 
  rewrite V_Arr in h1. rewrite C_def.
  destruct h1 as [[v1' [EQ h1]]|[e [EQ h1]]]; subst.
  + (* v1 is rec v1' *)
    split. 
    is_reducible.
    (* show that the application is in C τ' *)
    intros. inversion H. subst.
    next k. 
    eapply ih. auto. eauto.
    eapply dclosed; eauto.
  + (* v1 is abs e *) 
    split. is_reducible.
    intros. inversion H. subst.
    next k. 
    specialize (h1 v2 (S k) ltac:(auto)). 
    eapply h1.
    cbn.
    eapply dclosed; eauto.
Qed. 

Lemma ST_app v1 v2 A B k :
    Γ ⊨v v1 ∈ (Arr A B) @ k ->
    Γ ⊨v v2  ∈ A         @ k ->
    (* --------------- *)
    Γ ⊨ (app v1 v2) ∈ B @ k.
Proof.
  intros h1 h2.
  intros ρ i LE Hρ.
  asimpl.
  eapply C_app with (τ1 := A).
  eapply h1; eauto.
  eapply h2; eauto.
Qed.

Lemma ST_ret v τ k : 
  Γ ⊨v v ∈ τ @ k -> 
  (* ------------------------ *)
  Γ ⊨ (ret v) ∈ τ @ k.
Proof.
  intros h ρ i LE hρ.
  asimpl.
  eapply C_val.
  eapply h; eauto.
Qed.




Lemma C_let τ1 τ2 e2 k : forall e1,
  C τ1 e1 k -> 
  (forall v, (V τ1 v ⇒ C τ2 (let_ (ret v) e2)) k) -> 
  C τ2 (let_ e1 e2) k.
Proof.
  eapply strong_ind with 
    (P := fun k => forall e1,
              C τ1 e1 k -> 
              (forall v, (V τ1 v ⇒ C τ2 (let_ (ret v) e2)) k) -> 
              C τ2 (let_ e1 e2) k).
  clear k. intros k ih.
  intros e1 h1 h2.
  destruct (canstep e1) as [[e' hS]| IR].
  - eapply backwards. 
    eapply Small.s_let_cong; eauto.
    next k. specialize (ih k ltac:(auto)).
    eapply ih.
    eapply forwards'; eauto. 
    intros v. eapply dclosed; eauto.
  - rewrite C_def.
    split; auto.
    + extract_value v Vv EQ. subst.
      intro h.
      specialize (h2 v k ltac:(auto) Vv).
      extract_value v2 Vv2 EQ. subst. eauto.
    + intros e' SS. inversion SS; subst.
      * extract_value v1 Vv2 EQ. inversion EQ. subst.
        eapply forwards; eauto.
        eapply h2; eauto.
      * match goal with 
        | [IR : irreducible ?e1 , SS : ?e1 ~> ?e2 |- _ ] =>
             assert False; [eapply IR; eauto| done]
        end.
Qed.        


Lemma ST_let e1 e2 τ1 τ2 k : 
 Γ ⊨ e1 ∈ τ1 @ k -> 
 (τ1 .: Γ) ⊨ e2 ∈ τ2 @ k -> 
 Γ ⊨ let_ e1 e2 ∈ τ2 @ k.
Proof.
  intros h1 h2.
  intros ρ j LEj hρ.
  cbn.
  eapply C_let. eapply h1; eauto.
  intros v i LEi Vi.
  eapply backwards. eauto with rec.
  asimpl.
  eapply later. 
  eapply h2. lia.
  eapply semantic_subst_cons; eauto.
  eapply dclosed; eauto.
Qed.


End Semtyping. 

Import rec.typing.Notations.

Fixpoint soundness_tm {n} (Γ : Ctx n) e τ :
  Γ |-e e ∈ τ -> forall k, Γ ⊨ e ∈ τ @ k
with soundness_val {n} (Γ : Ctx n) v τ :
  Γ |-v v ∈ τ -> forall k, Γ ⊨v v ∈ τ @ k.
Proof. 
  all: intros h k; inversion h; subst.
  - eapply ST_ret; eauto.
  - eapply ST_let; eauto. 
  - eapply ST_app; eauto.
(* FILL IN HERE *) Admitted.

End Core.
