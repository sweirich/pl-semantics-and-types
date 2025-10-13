Require Import ssreflect.

Inductive Eff : Type := Top | Bot.

(** if either argument is Top, then the result is Top *)
Definition join (e1 : Eff) (e2 : Eff) : Eff :=
  match e1 , e2 with 
  | Bot , Bot => Bot
  | _ , _ => Top
  end.

(** Bot is less than Top *)
Definition le (e1 : Eff) (e2 : Eff) : Prop := 
  match e1, e2 with 
  | Bot , _ => True
  | _  , Top => True
  | _  , _ => False
  end.

Module Notations.
Notation "⊤" := Top.
Notation "⊥" := Bot.
Infix "⊕" := join (at level 70). 
Infix "<:" := le (at level 70).
End Notations.

Import Notations.

(** monoid: left and right identities, plus associativity *)
Lemma right_id e : e ⊕ ⊥ = e.
Proof. destruct e; done. Qed.

Lemma left_id e : ⊥ ⊕ e = e.
Proof. destruct e; done. Qed.

Lemma assoc e1 e2 e3 : ((e1 ⊕ e2) ⊕ e3) = (e1 ⊕ (e2 ⊕ e3)).
Proof. destruct e1; destruct e2; destruct e3; done. Qed.

(** pre-order: <: is reflexive and transitive *)
Lemma refl e : e <: e. 
Proof. destruct e; done. Qed.

Lemma trans e1 e2 e3 : e1 <: e2 -> e2 <: e3 -> e1 <: e3. 
Proof. destruct e1; destruct e2; destruct e3; done. Qed.

(** compatible: preorder is compatible with ⊕ *)
Lemma compat_right x y z : x <: y -> (z ⊕ x) <: (z ⊕ y).
Proof. destruct x; destruct y; destruct z; done. Qed.

Lemma compat_left x y z : x <: y -> (x ⊕ z) <: (y ⊕ z).
Proof. destruct x; destruct y; destruct z; done. Qed.

(* convenience: these properties can be proven from the
   lemmas above, for any definition of eff. 
   However, they are convenient for our 
   reasoning so we state them here. *)
Lemma compat x y z w : x <: y -> w <: z -> (x ⊕ w) <: (y ⊕ z).
Proof. destruct x; destruct y; destruct z; destruct w; done. Qed.

Lemma sub_left ε1 ε2 : ε1 <: (ε1 ⊕ ε2).
Proof. destruct ε1; destruct ε2; done. Qed.

Lemma sub_right ε1 ε2 : ε2 <: (ε1 ⊕ ε2).
Proof. destruct ε1; destruct ε2; done. Qed.

