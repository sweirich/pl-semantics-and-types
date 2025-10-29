(** * Imports *)

Require Export rec.reduction.

Open Scope rec_scope.
Import SyntaxNotations.

(** * Primitive reductions (i.e. beta steps) *)

Reserved Notation "e ~>> e'" (at level 70) .

Inductive primitive : Tm 0 -> Tm 0 -> Prop := 
  | s_beta : forall (e : Tm 1) (v : Val 0), 
      app (abs e) v ~>> e[v..]
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
  | s_app_rec : forall (v : Val 1) (v1 : Val 0), 
      app (rec v) v1 ~>> app v[(rec v)..] v1
  | s_prj_rec : forall (b : bool) (v : Val 1), 
      prj b (rec v) ~>> prj b v[(rec v)..]
  | s_unfold : forall v : Val 0, 
      unfold (fold v) ~>> ret v 
where "e ~>> e'" := (primitive e e').

Lemma primitive_deterministic :
  forall e e1 e2, e ~>> e1 -> e ~>> e2 -> e1 = e2.
Proof.
  intros e e1 e2 h1 h2.
  inversion h1; subst; inversion h2; subst; eauto.
Qed.
