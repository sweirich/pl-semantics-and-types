(** Running Time as an effect *)

From Stdlib Require Import ssreflect.
From Stdlib Require Import Arith.
From Stdlib Require Import Psatz.

Definition Eff := option nat.

Definition Bot : Eff := Some 0.
Definition One : Eff  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

(* This is DIV *)
Definition Top : Eff := None.

Definition join (e1 : Eff) (e2 : Eff) : Eff (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

Definition le (e1 : Eff) (e2 : Eff) : Prop (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

Module Notations.
Notation "⊤" := Top.
Notation "⊥" := Bot.
Infix "⊕" := join (at level 70). 
Infix "<:" := le (at level 70).
End Notations.

Import Notations.

(* monoid *)
Lemma right_id e : e ⊕ ⊥ = e.
(* FILL IN HERE *) Admitted.

Lemma left_id e : ⊥ ⊕ e = e.
(* FILL IN HERE *) Admitted.

Lemma assoc e1 e2 e3 : ((e1 ⊕ e2) ⊕ e3) = (e1 ⊕ (e2 ⊕ e3)).
(* FILL IN HERE *) Admitted.

(* pre-order *)
Lemma refl e : e <: e. 
(* FILL IN HERE *) Admitted.

Lemma trans e1 e2 e3 : e1 <: e2 -> e2 <: e3 -> e1 <: e3. 
(* FILL IN HERE *) Admitted.

(* compatible *)
Lemma compat_right x y z : x <: y -> (z ⊕ x) <: (z ⊕ y).
(* FILL IN HERE *) Admitted.

Lemma compat_left x y z : x <: y -> (x ⊕ z) <: (y ⊕ z).
(* FILL IN HERE *) Admitted.

(** convenience *)
Lemma compat x y z w : x <: y -> w <: z -> (x ⊕ w) <: (y ⊕ z).
(* FILL IN HERE *) Admitted.

Lemma bot_le x : ⊥ <: x.
(* FILL IN HERE *) Admitted.


