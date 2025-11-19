From Stdlib Require Import Lists.List FunctionalExtensionality.

Import List.ListNotations.

(** *  DLists *)

Definition dlist (A : Type) := list A -> list A.
Definition dnil {A} : dlist A := id.
Definition dcons {A} : A -> dlist A -> dlist A  := fun x dl => fun k => x :: dl k.
Definition dapp {A} : dlist A -> dlist A -> dlist A := fun f g => fun x => (f (g x)). 
Definition list_of_dlist {A} : dlist A -> list A := fun dl => dl [].

Lemma dlist_left_id {A} {dl : dlist A} : dapp dnil dl = dl.
(* FILL IN HERE *) Admitted.             
Lemma dlist_right_id {A} {dl : dlist A} : dapp dl dnil = dl.
(* FILL IN HERE *) Admitted.
Lemma dlist_assoc {A}{dl1 dl2 dl3 : dlist A} : 
  dapp (dapp dl1 dl2) dl3 = dapp dl1 (dapp dl2 dl3).
Proof. (* FILL IN HERE *) Admitted.

Fixpoint reverse_dlist {A} (xs : list A) : dlist A := 
  match xs with 
  | nil => dnil
  | y :: ys => dapp (reverse_dlist ys) (dcons y dnil)
  end.

Lemma reverse_dlist_spec {A} (xs : list A) : List.rev xs = list_of_dlist (reverse_dlist xs).
Proof. (* FILL IN HERE *) Admitted.


(** * Continuation Monad *)

Definition M (K A : Type) := (A -> K) -> K.
Definition ret {A K} : A -> M K A := fun x k => k x.
Definition bind {K A B} : M K A -> (A -> M K B) -> M K B := 
  fun m1 m2 => fun (k : B -> K) => m1 (fun a => m2 a k).

Infix ">>=" := bind (at level 70).
Notation "x <- m1 ;; m2" := (bind m1 (fun x => m2)) (at level 70).

(*
Left identity: return a >>= h ≡ h a
Right identity:	m >>= return ≡ m
Assoc: (m >>= g) >>= h ≡ m >>= (\x -> g x >>= h) 
*)

Lemma M_left_id {K A B}{x:A}{h : A -> M K B} : ret x >>= h = h x.
Proof.
(* FILL IN HERE *) Admitted.

Lemma M_right_id {K A}{x:A}{m : M K A} : m >>= ret = m.
Proof. (* FILL IN HERE *) Admitted.

Lemma M_assoc {K A B C}{m : M K A}{g : A -> M K B}{h : B -> M K C}  : 
  ((m >>= g) >>= h) = (m >>= (fun (x : A) => g x >>= h)).
Proof. (* FILL IN HERE *) Admitted.

Fixpoint reverse_cps {K A} (xs : list A) : M K (list A) := 
  match xs with 
  | nil => ret nil
  | y :: ys => zs <- reverse_cps ys ;; ret (zs ++ [y])
  end.


Lemma reverse_cps_spec {A} (xs: list A) : rev xs = reverse_cps xs (fun x => x).
Proof.  
(* FILL IN HERE *) Admitted.
