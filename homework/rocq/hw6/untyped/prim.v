(** * Imports *)

From Stdlib Require Export ssreflect.
From Stdlib Require Export Program.Equality.

Require Export common.core.
Require Export common.fintype.
Require Export common.fin_util.
Require Export common.relations.
Require Export common.renaming.

(** The syntax file defines notations for printing. However, this syntax can 
    sometimes be confusing so we disable it here. *)
Require Export untyped.syntax.
Disable Notation "↑__Val" (all).
Disable Notation "↑__Tm" (all).
Disable Notation "'__Val'" (all).
Disable Notation "var" (all).

(** Define a notation scope specific to this language. *)
Declare Scope rec_scope.

Module SyntaxNotations.
Export ScopedNotations.
Notation "'prj1'" := (prj true) (at level 70) : rec_scope.
Notation "'prj2'" := (prj false) (at level 70) : rec_scope.
Notation "'inj1'" := (inj true) (at level 70) : rec_scope.
Notation "'inj2'" := (inj false) (at level 70) : rec_scope.
Notation "⇑" := (up_Val_Val) : rec_scope.
Notation "⇑ σ" := (var var_zero .: σ >> ren_Val ↑) 
                    (only printing, at level 0) : rec_scope.
End SyntaxNotations.

Import SyntaxNotations.
Open Scope rec_scope.


(** * Syntax definition *)

(** Decide whether a value is a natural number value *)
Fixpoint is_nat (v : Val 0) : bool := 
  match v with 
  | zero => true
  | succ v1 => is_nat v1 
  | _ => false
  end.

Fixpoint to_nat (v : Val 0) : option nat := 
  match v with 
  | zero => Some 0
  | succ v1 => match to_nat v1 with 
                | Some k => Some (S k)
                | None => None
              end
  | _ => None
  end.



(** * Primitive reductions (i.e. beta steps) *)

Global Reserved Notation "e ~>> e'" (at level 70) .

Inductive primitive : Tm 0 -> Tm 0 -> Prop := 
  | s_beta : forall (e : Tm 2) (v : Val 0), 
      app (abs e) v ~>> e[v .: ((abs e)..)]
  | s_ifz_zero : forall (e1 : Tm 0) (e2 : Tm 1), 
      ifz zero e1 e2 ~>> e1
  | s_ifz_succ : forall (e1 : Tm 0) (e2 : Tm 1) (k : Val 0), 
      ifz (succ k) e1 e2 ~>> e2[k..]
  | s_prj1 : forall v1 v2 : Val 0, 
      prj1 (prod v1 v2) ~>> ret v1
  | s_prj2 : forall v1 v2 : Val 0, 
      prj2 (prod v1 v2) ~>> ret v2
  | s_case_inj1 : forall (v : Val 0) (e1 e2 : Tm 1), 
      case (inj1 v) e1 e2 ~>> e1[v..]
  | s_case_inj2 : forall (v : Val 0) (e1 e2 : Tm 1), 
      case (inj2 v) e1 e2 ~>> e2[v..]
where "e ~>> e'" := (primitive e e').

Lemma primitive_deterministic :
  forall e e1 e2, e ~>> e1 -> e ~>> e2 -> e1 = e2.
Proof.
  intros e e1 e2 h1 h2.
  inversion h1; subst; inversion h2; subst; eauto.
Qed.


