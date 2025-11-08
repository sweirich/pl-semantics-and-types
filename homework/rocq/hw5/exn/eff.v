Require Import ssreflect.

(** In this effect system, we represent effects as finite sets of exceptions that could possibly be raised by a computation. The effects are identified by by natural numbers. Therefore, we 
create a finite set of nats using Rocq's standard library definitions. The MSets library uses AVL trees to represent sets efficiently, but requires elements stored in the sets to be ordered. *)
From Stdlib Require Export MSets.  (* finite sets *)
From Stdlib Require Import Arith.  (* properties of nats *)
From Stdlib Require Import Structures.OrdersEx. (* nat is an ordered type. *)
Module NatSet := MSetList.Make OrdersEx.Nat_as_OT.


Definition Eff : Type := NatSet.t.
Definition Bot : Eff := NatSet.empty.
Definition join (e1 : Eff) (e2 : Eff) : Eff := NatSet.union e1 e2.
Definition le (e1 : Eff) (e2 : Eff) : Prop := NatSet.Subset e1 e2.
Definition lub (e1 : Eff) (e2 : Eff) : Eff := NatSet.union e1 e2.
Definition sub (e1 : Eff) (e2 : Eff) : Eff := NatSet.diff e1 e2.
Definition singleton (n : nat) := NatSet.singleton n.

(** Rocq's library includes the tactic 'fsetdec' (created by Penn PhD student
Aaron Bohannon) for reasoning about finite sets.  It can't solve everything,
but it is useful for working with expressions that involve effects. *)

From Stdlib Require Export MSets.MSetDecide.
Module NatSetTheory := MSetDecide.WDecideOn Nat NatSet.
Export NatSetTheory.

(* Make a special purpose tactic that unfolds first, then calls 
   the general solver *)
Global Ltac effdec := 
  unfold join,le,lub,sub,singleton in *; fsetdec.

Module Notations.
Notation "⊥" := Bot.
Infix "⊔" := lub (at level 70).
Infix "⊕" := join (at level 70). 
Infix "<:" := le (at level 70).
Infix "⊖"  := sub (at level 70).
Infix "≡"  := NatSet.Equal (at level 70).
End Notations.

Import Notations.

(** monoid: left and right identities, plus associativity *)
Lemma right_id e : e ⊕ ⊥ ≡ e.
Proof. effdec. Qed.

Lemma left_id e : ⊥ ⊕ e ≡ e.
Proof. effdec. Qed.

Lemma assoc e1 e2 e3 : ((e1 ⊕ e2) ⊕ e3) ≡ (e1 ⊕ (e2 ⊕ e3)).
Proof. effdec. Qed.

(** pre-order: <: is reflexive and transitive *)
Lemma refl e : e <: e.
Proof. effdec. Qed.

(** effdec can't solve this one directly. But we can give it some 
    help using the definition of <: *)
Lemma trans e1 e2 e3 : e1 <: e2 -> e2 <: e3 -> e1 <: e3. 
Proof. effdec. Qed.

(** compatible: preorder is compatible with ⊕ *)
Lemma compat_right x y z : x <: y -> (z ⊕ x) <: (z ⊕ y).
Proof. effdec. Qed.

Lemma compat_left x y z : x <: y -> (x ⊕ z) <: (y ⊕ z).
Proof. effdec. Qed.

(* convenience: these properties can be proven from the
   lemmas above, for any definition of eff. 
   However, they are convenient for our 
   reasoning so we state them here. *)
Lemma compat x y z w : x <: y -> w <: z -> (x ⊕ w) <: (y ⊕ z).
Proof. effdec. Qed.

Lemma sub_left ε1 ε2 : ε1 <: (ε1 ⊕ ε2).
Proof. effdec. Qed.

Lemma sub_right ε1 ε2 : ε2 <: (ε1 ⊕ ε2).
Proof. effdec. Qed.


