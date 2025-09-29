(** This file demonstrates the definition of a step-indexed logical 
    relation using well-founded recursion over natural number steps.

    To give this definition a convenient interface, we must use 
    the "proof_irrelevance" axiom that allows us to equate different 
    proofs of well-foundedness in our definition. 

    For convenience we also use propositional extensionality, which is
    how the Rocq standard library defines proof irrelevance.

*)

(* Axioms *)
(* From Stdlib Require Import Logic.FunctionalExtensionality. *)
From Stdlib Require Import Logic.PropExtensionality.

(* For reasoning about numbers *)
From Stdlib Require Import Arith.
From Stdlib Require Import Psatz.

(* Definitions about well-founded recursion *)
From Stdlib Require Import Init.Wf.

(* 
The Init.Wf module defines the [Acc] inductive datatype
which is the *accessibility* relation. The type [Acc R x] 
captures a general trace of all elements of A that are
that are related to [x] using the relation [R] in some 
finite number of steps. 

Inductive Acc (A : Type) (R : A -> A -> Prop) (x : A) : Prop :=  
    Acc_intro : (forall y : A, R y x -> Acc R y) -> Acc R x.

Well-founded recursion is defining a function by structural 
recursion on this datatype. Each recursive call can be made to 
any element that is accessible to the current one, as long 
as you can produce a proof of accessibility.

For example, if we are using the [<] relation on natural numbers
then the operation [Acc_inv] lets us create an accessibility 
proof for any number that is strictly less than [x].

Acc_inv : 
 forall [x : nat], Acc nat x -> forall [y : nat], y < x -> Acc lt y

To get the recursion started, we need a way to generate an 
accessibility proof for any number for the [lt] (i.e. [<]) relation.
This operation, [lt_wf] is found in the [Arith] library.

lt_wf : forall (x : nat) : Acc lt x

*)


Require Export common.core.
Require Export rec.steps.
Import reduction.Notations.
Import iprop.Notations.

(* We put these definitions in a Module so that Rocq can check that 
   they match our previous assumptions about the definitions that 
   we made in rec.steps. *)
Module LR : LogicalRelation.

(** To make the definitions more similar to our axiomatization. We 
    define two operations that are analogous to iLater and iImp. 
    The difference is that in addition to a step count, they also 
    require an accessibility proof for that step count.
*)

Definition iaProp := forall n, Acc lt n -> Prop.

Definition later : iaProp -> iaProp :=
fun ϕ => fun k : nat =>
 match k as n return (Acc lt n -> Prop) with
 | 0 => fun _ : Acc lt 0 => True
 | S n => fun (ACC : Acc lt (S n)) => ϕ n (Acc_inv ACC (le_n (S n)))
 end.


(** This definition requires well-founded recursion. *)
Definition implies : iaProp -> iaProp -> iaProp := 
  fun ϕ ψ k ACC => 
    forall j (pf: j < k),  ϕ j (Acc_inv ACC pf) -> ψ j (Acc_inv ACC pf).

(* TODO: fix ACC uses here. This is almost an equivalent version.
Definition implies' : iaProp -> iaProp -> iaProp := 
  fun ϕ ψ k ACC => 
    forall j (pf: j <= k),  later ϕ j (Acc_inv ACC pf) -> later ψ j (Acc_inv ACC pf).
*)

(** Even though C' could be defined by structural induction on k, we still need 
    the accessibility relation for the recursive call to V. So we can define
    this Fixpoint using struct ACC. *)
Fixpoint C' (V : Val 0 -> iaProp) (e : Tm 0) (k : nat) ACC {struct ACC} : Prop := 
  (irreducible e -> exists v, e = ret v /\ V v k ACC) /\ 
      (forall e', e ~> e' -> later (C' V e') k ACC).
                      
(** The Arr case requires well-founded recursion. *)
Fixpoint V' (t : Ty 0) (v : Val 0) k (ACC : Acc lt k) {struct ACC} := 
    match t with 
    | Void => False 

    | Nat => (exists n, v = lit n)

    | Arr t1 t2 => 
       (exists v2, v = rec v2 /\ later (V' (Arr t1 t2) (v2[v..])) k ACC) \/
       (exists e,  v = abs e /\ forall v1, 
             implies (V' t1 v1) (C' (V' t2) e[v1..]) k ACC)

    | Prod t1 t2 => 
      (exists v2, v = rec v2 /\ later (V' (Prod t1 t2) (v2[v..])) k ACC) \/
      (exists v1 v2, v = prod v1 v2 /\ later (V' t1 v1) k ACC /\ later (V' t2 v2) k ACC)

    | Sum τ1 τ2 => 
         (exists v1, v = inj true v1 /\ later (V' τ1 v1) k ACC) \/
         (exists v2, v = inj false v2 /\ later (V' τ2 v2) k ACC)

    | Mu τ => 
         (exists v2, v = fold v2 /\
             (later (V' (τ [(Mu τ)..]) v2)) k ACC)
    | _ => False
end.

(* For our top level definitions, we provide the accessibility proof 
   for lt on natural numbers. *)
Definition V t v k := V' t v k (lt_wf k).

Definition C τ e k := C' (V' τ) e k (lt_wf k).

(** Now we prove all of the unfoldings, hiding the accessibility proofs
    using our top-level definitions. *)
Lemma V_Void v k : V Void v k = False.
unfold V. cbn. done. Qed.

Lemma V_Nat v k : V Nat v k = exists n, v = lit n.
unfold V. cbn. done. Qed.

Lemma V_Arr  : forall τ1 τ2 v k, 
    V (Arr τ1 τ2) v k = 
         ((exists v2, v = rec v2 /\ 
             (▷ (V (Arr τ1 τ2) (v2[v..])) k)) \/ 
         (exists e,  v = abs e  /\ 
             (forall v1, (▷ (V τ1 v1) ⇒ (▷ (C τ2 e[v1..]))) k))).
Proof.
  intros.
  unfold V. destruct lt_wf.
  unfold V'. fold V'.
  f_equal.
  unfold later, iLater, implies. destruct k. done.
  have I: (Acc_inv (Acc_intro (S k) a) (le_n (S k))) = (lt_wf k).
  { eapply proof_irrelevance. } 
  rewrite I. done.
  unfold iLater, iImp.
  eapply propositional_extensionality.
  split.
  + move=> [e [EQ h]]. exists e. split; auto.
    intros v1 j LE. destruct j. done.
    have pf : j < k . lia.
    specialize (h v1 j pf).
    have I: (Acc_inv (Acc_intro k a) pf) = (lt_wf j). eapply proof_irrelevance.
    rewrite I in h.
    unfold C. done.
  + move=> [e [EQ h]]. exists e. split; auto.
    intros v1 j LE. 
    have pf : S j <= k . lia.
    specialize (h v1 (S j) pf). 
    have I: (Acc_inv (Acc_intro k a) LE) = (lt_wf j). eapply proof_irrelevance.
    rewrite I. eapply h.
Qed.


Lemma V_Prod : forall τ1 τ2 v k, 
    V (Prod τ1 τ2) v k = 
         ((exists v2, v = rec v2 /\ 
             (▷ (V (Prod τ1 τ2) (v2[v..]))) k) \/ 
         (exists v1 v2,  v = prod v1 v2  /\ 
              ▷ (V τ1 v1) k /\  ▷ (V τ2 v2) k)).
Proof.
  unfold V. intros τ1 τ2 v k.
  destruct lt_wf. unfold V'. fold V'.
  unfold later, iLater.
  destruct k.
  - done.
  - have EQ: ((Acc_inv (Acc_intro (S k) a) (le_n (S k))) = 
               (lt_wf k)).
    eapply proof_irrelevance.
    rewrite EQ. done.
Qed.

Lemma V_Sum : forall τ1 τ2 v k, 
    V (Sum τ1 τ2) v k = 
         ((exists v1, v = inj true v1 /\ ▷ (V τ1 v1) k) \/
         (exists v2, v = inj false v2 /\ ▷ (V τ2 v2) k)).
Proof.
  unfold V. intros τ1 τ2 v k.
  destruct lt_wf. unfold V'. fold V'.
  unfold later, iLater.
  destruct k.
  - done.
  - have EQ: ((Acc_inv (Acc_intro (S k) a) (le_n (S k))) = 
               (lt_wf k)).
    eapply proof_irrelevance.
    rewrite EQ. done.
Qed.

Lemma V_Mu : forall τ v k,
    V (Mu τ) v k = (exists v2, v = fold v2 /\
                            (▷ (V (τ [(Mu τ)..]) v2)) k).  
Proof.
 unfold V. intros τ v k.
  destruct lt_wf. unfold V'. fold V'.
  unfold later, iLater.
  destruct k.
  - done.
  - have EQ: ((Acc_inv (Acc_intro (S k) a) (le_n (S k))) = 
               (lt_wf k)).
    eapply proof_irrelevance.
    rewrite EQ. done.
Qed.

Lemma C_def τ e k : 
  C τ e k = 
    ((irreducible e -> exists v, e = ret v /\ (V τ v k)) /\
       (forall e', Small.step e e' -> ▷ (C τ e') k)).
Proof.
  unfold C. unfold V.  unfold C'.
  unfold later, iLater.  
  destruct k. destruct (lt_wf 0).  done.
  destruct (lt_wf (S k)).
  have EQ: (Acc_inv (Acc_intro (S k) a) (le_n (S k))) = (lt_wf k).
  { eapply proof_irrelevance. } 
  rewrite EQ. done.
Qed.

End LR.

