Require Import core fintype.

Require Import Setoid Morphisms Relation_Definitions.


Module Core.

Inductive Val (n_Val : nat) : Type :=
  | var : fin n_Val -> Val n_Val
  | zero : Val n_Val
  | succ : Val n_Val -> Val n_Val
  | prod : Val n_Val -> Val n_Val -> Val n_Val
  | inj : bool -> Val n_Val -> Val n_Val
  | abs : Tm (S n_Val) -> Val n_Val
  | rec : Val (S n_Val) -> Val n_Val
  | fold : Val n_Val -> Val n_Val
with Tm (n_Val : nat) : Type :=
  | ret : Val n_Val -> Tm n_Val
  | let_ : Tm n_Val -> Tm (S n_Val) -> Tm n_Val
  | ifz : Val n_Val -> Tm n_Val -> Tm (S n_Val) -> Tm n_Val
  | prj : bool -> Val n_Val -> Tm n_Val
  | split : Val n_Val -> Tm (S (S n_Val)) -> Tm n_Val
  | case : Val n_Val -> Tm (S n_Val) -> Tm (S n_Val) -> Tm n_Val
  | app : Val n_Val -> Val n_Val -> Tm n_Val
  | unfold : Val n_Val -> Tm n_Val
  | box : Val n_Val -> Tm n_Val
  | bind : Tm n_Val -> Tm (S n_Val) -> Tm n_Val.

Lemma congr_zero {m_Val : nat} : zero m_Val = zero m_Val.
Proof.
exact (eq_refl).
Qed.

Lemma congr_succ {m_Val : nat} {s0 : Val m_Val} {t0 : Val m_Val}
  (H0 : s0 = t0) : succ m_Val s0 = succ m_Val t0.
Proof.
exact (eq_trans eq_refl (ap (fun x => succ m_Val x) H0)).
Qed.

Lemma congr_prod {m_Val : nat} {s0 : Val m_Val} {s1 : Val m_Val}
  {t0 : Val m_Val} {t1 : Val m_Val} (H0 : s0 = t0) (H1 : s1 = t1) :
  prod m_Val s0 s1 = prod m_Val t0 t1.
Proof.
exact (eq_trans (eq_trans eq_refl (ap (fun x => prod m_Val x s1) H0))
         (ap (fun x => prod m_Val t0 x) H1)).
Qed.

Lemma congr_inj {m_Val : nat} {s0 : bool} {s1 : Val m_Val} {t0 : bool}
  {t1 : Val m_Val} (H0 : s0 = t0) (H1 : s1 = t1) :
  inj m_Val s0 s1 = inj m_Val t0 t1.
Proof.
exact (eq_trans (eq_trans eq_refl (ap (fun x => inj m_Val x s1) H0))
         (ap (fun x => inj m_Val t0 x) H1)).
Qed.

Lemma congr_abs {m_Val : nat} {s0 : Tm (S m_Val)} {t0 : Tm (S m_Val)}
  (H0 : s0 = t0) : abs m_Val s0 = abs m_Val t0.
Proof.
exact (eq_trans eq_refl (ap (fun x => abs m_Val x) H0)).
Qed.

Lemma congr_rec {m_Val : nat} {s0 : Val (S m_Val)} {t0 : Val (S m_Val)}
  (H0 : s0 = t0) : rec m_Val s0 = rec m_Val t0.
Proof.
exact (eq_trans eq_refl (ap (fun x => rec m_Val x) H0)).
Qed.

Lemma congr_fold {m_Val : nat} {s0 : Val m_Val} {t0 : Val m_Val}
  (H0 : s0 = t0) : fold m_Val s0 = fold m_Val t0.
Proof.
exact (eq_trans eq_refl (ap (fun x => fold m_Val x) H0)).
Qed.

Lemma congr_ret {m_Val : nat} {s0 : Val m_Val} {t0 : Val m_Val}
  (H0 : s0 = t0) : ret m_Val s0 = ret m_Val t0.
Proof.
exact (eq_trans eq_refl (ap (fun x => ret m_Val x) H0)).
Qed.

Lemma congr_let_ {m_Val : nat} {s0 : Tm m_Val} {s1 : Tm (S m_Val)}
  {t0 : Tm m_Val} {t1 : Tm (S m_Val)} (H0 : s0 = t0) (H1 : s1 = t1) :
  let_ m_Val s0 s1 = let_ m_Val t0 t1.
Proof.
exact (eq_trans (eq_trans eq_refl (ap (fun x => let_ m_Val x s1) H0))
         (ap (fun x => let_ m_Val t0 x) H1)).
Qed.

Lemma congr_ifz {m_Val : nat} {s0 : Val m_Val} {s1 : Tm m_Val}
  {s2 : Tm (S m_Val)} {t0 : Val m_Val} {t1 : Tm m_Val} {t2 : Tm (S m_Val)}
  (H0 : s0 = t0) (H1 : s1 = t1) (H2 : s2 = t2) :
  ifz m_Val s0 s1 s2 = ifz m_Val t0 t1 t2.
Proof.
exact (eq_trans
         (eq_trans (eq_trans eq_refl (ap (fun x => ifz m_Val x s1 s2) H0))
            (ap (fun x => ifz m_Val t0 x s2) H1))
         (ap (fun x => ifz m_Val t0 t1 x) H2)).
Qed.

Lemma congr_prj {m_Val : nat} {s0 : bool} {s1 : Val m_Val} {t0 : bool}
  {t1 : Val m_Val} (H0 : s0 = t0) (H1 : s1 = t1) :
  prj m_Val s0 s1 = prj m_Val t0 t1.
Proof.
exact (eq_trans (eq_trans eq_refl (ap (fun x => prj m_Val x s1) H0))
         (ap (fun x => prj m_Val t0 x) H1)).
Qed.

Lemma congr_split {m_Val : nat} {s0 : Val m_Val} {s1 : Tm (S (S m_Val))}
  {t0 : Val m_Val} {t1 : Tm (S (S m_Val))} (H0 : s0 = t0) (H1 : s1 = t1) :
  split m_Val s0 s1 = split m_Val t0 t1.
Proof.
exact (eq_trans (eq_trans eq_refl (ap (fun x => split m_Val x s1) H0))
         (ap (fun x => split m_Val t0 x) H1)).
Qed.

Lemma congr_case {m_Val : nat} {s0 : Val m_Val} {s1 : Tm (S m_Val)}
  {s2 : Tm (S m_Val)} {t0 : Val m_Val} {t1 : Tm (S m_Val)}
  {t2 : Tm (S m_Val)} (H0 : s0 = t0) (H1 : s1 = t1) (H2 : s2 = t2) :
  case m_Val s0 s1 s2 = case m_Val t0 t1 t2.
Proof.
exact (eq_trans
         (eq_trans (eq_trans eq_refl (ap (fun x => case m_Val x s1 s2) H0))
            (ap (fun x => case m_Val t0 x s2) H1))
         (ap (fun x => case m_Val t0 t1 x) H2)).
Qed.

Lemma congr_app {m_Val : nat} {s0 : Val m_Val} {s1 : Val m_Val}
  {t0 : Val m_Val} {t1 : Val m_Val} (H0 : s0 = t0) (H1 : s1 = t1) :
  app m_Val s0 s1 = app m_Val t0 t1.
Proof.
exact (eq_trans (eq_trans eq_refl (ap (fun x => app m_Val x s1) H0))
         (ap (fun x => app m_Val t0 x) H1)).
Qed.

Lemma congr_unfold {m_Val : nat} {s0 : Val m_Val} {t0 : Val m_Val}
  (H0 : s0 = t0) : unfold m_Val s0 = unfold m_Val t0.
Proof.
exact (eq_trans eq_refl (ap (fun x => unfold m_Val x) H0)).
Qed.

Lemma congr_box {m_Val : nat} {s0 : Val m_Val} {t0 : Val m_Val}
  (H0 : s0 = t0) : box m_Val s0 = box m_Val t0.
Proof.
exact (eq_trans eq_refl (ap (fun x => box m_Val x) H0)).
Qed.

Lemma congr_bind {m_Val : nat} {s0 : Tm m_Val} {s1 : Tm (S m_Val)}
  {t0 : Tm m_Val} {t1 : Tm (S m_Val)} (H0 : s0 = t0) (H1 : s1 = t1) :
  bind m_Val s0 s1 = bind m_Val t0 t1.
Proof.
exact (eq_trans (eq_trans eq_refl (ap (fun x => bind m_Val x s1) H0))
         (ap (fun x => bind m_Val t0 x) H1)).
Qed.

Lemma upRen_Val_Val {m : nat} {n : nat} (xi : fin m -> fin n) :
  fin (S m) -> fin (S n).
Proof.
exact (up_ren xi).
Defined.

Lemma upRen_list_Val_Val (p : nat) {m : nat} {n : nat} (xi : fin m -> fin n)
  : fin (plus p m) -> fin (plus p n).
Proof.
exact (upRen_p p xi).
Defined.

Fixpoint ren_Val {m_Val : nat} {n_Val : nat}
(xi_Val : fin m_Val -> fin n_Val) (s : Val m_Val) {struct s} : Val n_Val :=
  match s with
  | var _ s0 => var n_Val (xi_Val s0)
  | zero _ => zero n_Val
  | succ _ s0 => succ n_Val (ren_Val xi_Val s0)
  | prod _ s0 s1 => prod n_Val (ren_Val xi_Val s0) (ren_Val xi_Val s1)
  | inj _ s0 s1 => inj n_Val s0 (ren_Val xi_Val s1)
  | abs _ s0 => abs n_Val (ren_Tm (upRen_Val_Val xi_Val) s0)
  | rec _ s0 => rec n_Val (ren_Val (upRen_Val_Val xi_Val) s0)
  | fold _ s0 => fold n_Val (ren_Val xi_Val s0)
  end
with ren_Tm {m_Val : nat} {n_Val : nat} (xi_Val : fin m_Val -> fin n_Val)
(s : Tm m_Val) {struct s} : Tm n_Val :=
  match s with
  | ret _ s0 => ret n_Val (ren_Val xi_Val s0)
  | let_ _ s0 s1 =>
      let_ n_Val (ren_Tm xi_Val s0) (ren_Tm (upRen_Val_Val xi_Val) s1)
  | ifz _ s0 s1 s2 =>
      ifz n_Val (ren_Val xi_Val s0) (ren_Tm xi_Val s1)
        (ren_Tm (upRen_Val_Val xi_Val) s2)
  | prj _ s0 s1 => prj n_Val s0 (ren_Val xi_Val s1)
  | split _ s0 s1 =>
      split n_Val (ren_Val xi_Val s0)
        (ren_Tm (upRen_Val_Val (upRen_Val_Val xi_Val)) s1)
  | case _ s0 s1 s2 =>
      case n_Val (ren_Val xi_Val s0) (ren_Tm (upRen_Val_Val xi_Val) s1)
        (ren_Tm (upRen_Val_Val xi_Val) s2)
  | app _ s0 s1 => app n_Val (ren_Val xi_Val s0) (ren_Val xi_Val s1)
  | unfold _ s0 => unfold n_Val (ren_Val xi_Val s0)
  | box _ s0 => box n_Val (ren_Val xi_Val s0)
  | bind _ s0 s1 =>
      bind n_Val (ren_Tm xi_Val s0) (ren_Tm (upRen_Val_Val xi_Val) s1)
  end.

Lemma up_Val_Val {m : nat} {n_Val : nat} (sigma : fin m -> Val n_Val) :
  fin (S m) -> Val (S n_Val).
Proof.
exact (scons (var (S n_Val) var_zero) (funcomp (ren_Val shift) sigma)).
Defined.

Lemma up_list_Val_Val (p : nat) {m : nat} {n_Val : nat}
  (sigma : fin m -> Val n_Val) : fin (plus p m) -> Val (plus p n_Val).
Proof.
exact (scons_p p (funcomp (var (plus p n_Val)) (zero_p p))
         (funcomp (ren_Val (shift_p p)) sigma)).
Defined.

Fixpoint subst_Val {m_Val : nat} {n_Val : nat}
(sigma_Val : fin m_Val -> Val n_Val) (s : Val m_Val) {struct s} : Val n_Val
:=
  match s with
  | var _ s0 => sigma_Val s0
  | zero _ => zero n_Val
  | succ _ s0 => succ n_Val (subst_Val sigma_Val s0)
  | prod _ s0 s1 =>
      prod n_Val (subst_Val sigma_Val s0) (subst_Val sigma_Val s1)
  | inj _ s0 s1 => inj n_Val s0 (subst_Val sigma_Val s1)
  | abs _ s0 => abs n_Val (subst_Tm (up_Val_Val sigma_Val) s0)
  | rec _ s0 => rec n_Val (subst_Val (up_Val_Val sigma_Val) s0)
  | fold _ s0 => fold n_Val (subst_Val sigma_Val s0)
  end
with subst_Tm {m_Val : nat} {n_Val : nat}
(sigma_Val : fin m_Val -> Val n_Val) (s : Tm m_Val) {struct s} : Tm n_Val :=
  match s with
  | ret _ s0 => ret n_Val (subst_Val sigma_Val s0)
  | let_ _ s0 s1 =>
      let_ n_Val (subst_Tm sigma_Val s0) (subst_Tm (up_Val_Val sigma_Val) s1)
  | ifz _ s0 s1 s2 =>
      ifz n_Val (subst_Val sigma_Val s0) (subst_Tm sigma_Val s1)
        (subst_Tm (up_Val_Val sigma_Val) s2)
  | prj _ s0 s1 => prj n_Val s0 (subst_Val sigma_Val s1)
  | split _ s0 s1 =>
      split n_Val (subst_Val sigma_Val s0)
        (subst_Tm (up_Val_Val (up_Val_Val sigma_Val)) s1)
  | case _ s0 s1 s2 =>
      case n_Val (subst_Val sigma_Val s0)
        (subst_Tm (up_Val_Val sigma_Val) s1)
        (subst_Tm (up_Val_Val sigma_Val) s2)
  | app _ s0 s1 =>
      app n_Val (subst_Val sigma_Val s0) (subst_Val sigma_Val s1)
  | unfold _ s0 => unfold n_Val (subst_Val sigma_Val s0)
  | box _ s0 => box n_Val (subst_Val sigma_Val s0)
  | bind _ s0 s1 =>
      bind n_Val (subst_Tm sigma_Val s0) (subst_Tm (up_Val_Val sigma_Val) s1)
  end.

Lemma upId_Val_Val {m_Val : nat} (sigma : fin m_Val -> Val m_Val)
  (Eq : forall x, sigma x = var m_Val x) :
  forall x, up_Val_Val sigma x = var (S m_Val) x.
Proof.
exact (fun n =>
       match n with
       | Some fin_n => ap (ren_Val shift) (Eq fin_n)
       | None => eq_refl
       end).
Qed.

Lemma upId_list_Val_Val {p : nat} {m_Val : nat}
  (sigma : fin m_Val -> Val m_Val) (Eq : forall x, sigma x = var m_Val x) :
  forall x, up_list_Val_Val p sigma x = var (plus p m_Val) x.
Proof.
exact (fun n =>
       scons_p_eta (var (plus p m_Val))
         (fun n => ap (ren_Val (shift_p p)) (Eq n)) (fun n => eq_refl)).
Qed.

Fixpoint idSubst_Val {m_Val : nat} (sigma_Val : fin m_Val -> Val m_Val)
(Eq_Val : forall x, sigma_Val x = var m_Val x) (s : Val m_Val) {struct s} :
subst_Val sigma_Val s = s :=
  match s with
  | var _ s0 => Eq_Val s0
  | zero _ => congr_zero
  | succ _ s0 => congr_succ (idSubst_Val sigma_Val Eq_Val s0)
  | prod _ s0 s1 =>
      congr_prod (idSubst_Val sigma_Val Eq_Val s0)
        (idSubst_Val sigma_Val Eq_Val s1)
  | inj _ s0 s1 => congr_inj (eq_refl s0) (idSubst_Val sigma_Val Eq_Val s1)
  | abs _ s0 =>
      congr_abs
        (idSubst_Tm (up_Val_Val sigma_Val) (upId_Val_Val _ Eq_Val) s0)
  | rec _ s0 =>
      congr_rec
        (idSubst_Val (up_Val_Val sigma_Val) (upId_Val_Val _ Eq_Val) s0)
  | fold _ s0 => congr_fold (idSubst_Val sigma_Val Eq_Val s0)
  end
with idSubst_Tm {m_Val : nat} (sigma_Val : fin m_Val -> Val m_Val)
(Eq_Val : forall x, sigma_Val x = var m_Val x) (s : Tm m_Val) {struct s} :
subst_Tm sigma_Val s = s :=
  match s with
  | ret _ s0 => congr_ret (idSubst_Val sigma_Val Eq_Val s0)
  | let_ _ s0 s1 =>
      congr_let_ (idSubst_Tm sigma_Val Eq_Val s0)
        (idSubst_Tm (up_Val_Val sigma_Val) (upId_Val_Val _ Eq_Val) s1)
  | ifz _ s0 s1 s2 =>
      congr_ifz (idSubst_Val sigma_Val Eq_Val s0)
        (idSubst_Tm sigma_Val Eq_Val s1)
        (idSubst_Tm (up_Val_Val sigma_Val) (upId_Val_Val _ Eq_Val) s2)
  | prj _ s0 s1 => congr_prj (eq_refl s0) (idSubst_Val sigma_Val Eq_Val s1)
  | split _ s0 s1 =>
      congr_split (idSubst_Val sigma_Val Eq_Val s0)
        (idSubst_Tm (up_Val_Val (up_Val_Val sigma_Val))
           (upId_Val_Val _ (upId_Val_Val _ Eq_Val)) s1)
  | case _ s0 s1 s2 =>
      congr_case (idSubst_Val sigma_Val Eq_Val s0)
        (idSubst_Tm (up_Val_Val sigma_Val) (upId_Val_Val _ Eq_Val) s1)
        (idSubst_Tm (up_Val_Val sigma_Val) (upId_Val_Val _ Eq_Val) s2)
  | app _ s0 s1 =>
      congr_app (idSubst_Val sigma_Val Eq_Val s0)
        (idSubst_Val sigma_Val Eq_Val s1)
  | unfold _ s0 => congr_unfold (idSubst_Val sigma_Val Eq_Val s0)
  | box _ s0 => congr_box (idSubst_Val sigma_Val Eq_Val s0)
  | bind _ s0 s1 =>
      congr_bind (idSubst_Tm sigma_Val Eq_Val s0)
        (idSubst_Tm (up_Val_Val sigma_Val) (upId_Val_Val _ Eq_Val) s1)
  end.

Lemma upExtRen_Val_Val {m : nat} {n : nat} (xi : fin m -> fin n)
  (zeta : fin m -> fin n) (Eq : forall x, xi x = zeta x) :
  forall x, upRen_Val_Val xi x = upRen_Val_Val zeta x.
Proof.
exact (fun n =>
       match n with
       | Some fin_n => ap shift (Eq fin_n)
       | None => eq_refl
       end).
Qed.

Lemma upExtRen_list_Val_Val {p : nat} {m : nat} {n : nat}
  (xi : fin m -> fin n) (zeta : fin m -> fin n)
  (Eq : forall x, xi x = zeta x) :
  forall x, upRen_list_Val_Val p xi x = upRen_list_Val_Val p zeta x.
Proof.
exact (fun n =>
       scons_p_congr (fun n => eq_refl) (fun n => ap (shift_p p) (Eq n))).
Qed.

Fixpoint extRen_Val {m_Val : nat} {n_Val : nat}
(xi_Val : fin m_Val -> fin n_Val) (zeta_Val : fin m_Val -> fin n_Val)
(Eq_Val : forall x, xi_Val x = zeta_Val x) (s : Val m_Val) {struct s} :
ren_Val xi_Val s = ren_Val zeta_Val s :=
  match s with
  | var _ s0 => ap (var n_Val) (Eq_Val s0)
  | zero _ => congr_zero
  | succ _ s0 => congr_succ (extRen_Val xi_Val zeta_Val Eq_Val s0)
  | prod _ s0 s1 =>
      congr_prod (extRen_Val xi_Val zeta_Val Eq_Val s0)
        (extRen_Val xi_Val zeta_Val Eq_Val s1)
  | inj _ s0 s1 =>
      congr_inj (eq_refl s0) (extRen_Val xi_Val zeta_Val Eq_Val s1)
  | abs _ s0 =>
      congr_abs
        (extRen_Tm (upRen_Val_Val xi_Val) (upRen_Val_Val zeta_Val)
           (upExtRen_Val_Val _ _ Eq_Val) s0)
  | rec _ s0 =>
      congr_rec
        (extRen_Val (upRen_Val_Val xi_Val) (upRen_Val_Val zeta_Val)
           (upExtRen_Val_Val _ _ Eq_Val) s0)
  | fold _ s0 => congr_fold (extRen_Val xi_Val zeta_Val Eq_Val s0)
  end
with extRen_Tm {m_Val : nat} {n_Val : nat} (xi_Val : fin m_Val -> fin n_Val)
(zeta_Val : fin m_Val -> fin n_Val)
(Eq_Val : forall x, xi_Val x = zeta_Val x) (s : Tm m_Val) {struct s} :
ren_Tm xi_Val s = ren_Tm zeta_Val s :=
  match s with
  | ret _ s0 => congr_ret (extRen_Val xi_Val zeta_Val Eq_Val s0)
  | let_ _ s0 s1 =>
      congr_let_ (extRen_Tm xi_Val zeta_Val Eq_Val s0)
        (extRen_Tm (upRen_Val_Val xi_Val) (upRen_Val_Val zeta_Val)
           (upExtRen_Val_Val _ _ Eq_Val) s1)
  | ifz _ s0 s1 s2 =>
      congr_ifz (extRen_Val xi_Val zeta_Val Eq_Val s0)
        (extRen_Tm xi_Val zeta_Val Eq_Val s1)
        (extRen_Tm (upRen_Val_Val xi_Val) (upRen_Val_Val zeta_Val)
           (upExtRen_Val_Val _ _ Eq_Val) s2)
  | prj _ s0 s1 =>
      congr_prj (eq_refl s0) (extRen_Val xi_Val zeta_Val Eq_Val s1)
  | split _ s0 s1 =>
      congr_split (extRen_Val xi_Val zeta_Val Eq_Val s0)
        (extRen_Tm (upRen_Val_Val (upRen_Val_Val xi_Val))
           (upRen_Val_Val (upRen_Val_Val zeta_Val))
           (upExtRen_Val_Val _ _ (upExtRen_Val_Val _ _ Eq_Val)) s1)
  | case _ s0 s1 s2 =>
      congr_case (extRen_Val xi_Val zeta_Val Eq_Val s0)
        (extRen_Tm (upRen_Val_Val xi_Val) (upRen_Val_Val zeta_Val)
           (upExtRen_Val_Val _ _ Eq_Val) s1)
        (extRen_Tm (upRen_Val_Val xi_Val) (upRen_Val_Val zeta_Val)
           (upExtRen_Val_Val _ _ Eq_Val) s2)
  | app _ s0 s1 =>
      congr_app (extRen_Val xi_Val zeta_Val Eq_Val s0)
        (extRen_Val xi_Val zeta_Val Eq_Val s1)
  | unfold _ s0 => congr_unfold (extRen_Val xi_Val zeta_Val Eq_Val s0)
  | box _ s0 => congr_box (extRen_Val xi_Val zeta_Val Eq_Val s0)
  | bind _ s0 s1 =>
      congr_bind (extRen_Tm xi_Val zeta_Val Eq_Val s0)
        (extRen_Tm (upRen_Val_Val xi_Val) (upRen_Val_Val zeta_Val)
           (upExtRen_Val_Val _ _ Eq_Val) s1)
  end.

Lemma upExt_Val_Val {m : nat} {n_Val : nat} (sigma : fin m -> Val n_Val)
  (tau : fin m -> Val n_Val) (Eq : forall x, sigma x = tau x) :
  forall x, up_Val_Val sigma x = up_Val_Val tau x.
Proof.
exact (fun n =>
       match n with
       | Some fin_n => ap (ren_Val shift) (Eq fin_n)
       | None => eq_refl
       end).
Qed.

Lemma upExt_list_Val_Val {p : nat} {m : nat} {n_Val : nat}
  (sigma : fin m -> Val n_Val) (tau : fin m -> Val n_Val)
  (Eq : forall x, sigma x = tau x) :
  forall x, up_list_Val_Val p sigma x = up_list_Val_Val p tau x.
Proof.
exact (fun n =>
       scons_p_congr (fun n => eq_refl)
         (fun n => ap (ren_Val (shift_p p)) (Eq n))).
Qed.

Fixpoint ext_Val {m_Val : nat} {n_Val : nat}
(sigma_Val : fin m_Val -> Val n_Val) (tau_Val : fin m_Val -> Val n_Val)
(Eq_Val : forall x, sigma_Val x = tau_Val x) (s : Val m_Val) {struct s} :
subst_Val sigma_Val s = subst_Val tau_Val s :=
  match s with
  | var _ s0 => Eq_Val s0
  | zero _ => congr_zero
  | succ _ s0 => congr_succ (ext_Val sigma_Val tau_Val Eq_Val s0)
  | prod _ s0 s1 =>
      congr_prod (ext_Val sigma_Val tau_Val Eq_Val s0)
        (ext_Val sigma_Val tau_Val Eq_Val s1)
  | inj _ s0 s1 =>
      congr_inj (eq_refl s0) (ext_Val sigma_Val tau_Val Eq_Val s1)
  | abs _ s0 =>
      congr_abs
        (ext_Tm (up_Val_Val sigma_Val) (up_Val_Val tau_Val)
           (upExt_Val_Val _ _ Eq_Val) s0)
  | rec _ s0 =>
      congr_rec
        (ext_Val (up_Val_Val sigma_Val) (up_Val_Val tau_Val)
           (upExt_Val_Val _ _ Eq_Val) s0)
  | fold _ s0 => congr_fold (ext_Val sigma_Val tau_Val Eq_Val s0)
  end
with ext_Tm {m_Val : nat} {n_Val : nat} (sigma_Val : fin m_Val -> Val n_Val)
(tau_Val : fin m_Val -> Val n_Val)
(Eq_Val : forall x, sigma_Val x = tau_Val x) (s : Tm m_Val) {struct s} :
subst_Tm sigma_Val s = subst_Tm tau_Val s :=
  match s with
  | ret _ s0 => congr_ret (ext_Val sigma_Val tau_Val Eq_Val s0)
  | let_ _ s0 s1 =>
      congr_let_ (ext_Tm sigma_Val tau_Val Eq_Val s0)
        (ext_Tm (up_Val_Val sigma_Val) (up_Val_Val tau_Val)
           (upExt_Val_Val _ _ Eq_Val) s1)
  | ifz _ s0 s1 s2 =>
      congr_ifz (ext_Val sigma_Val tau_Val Eq_Val s0)
        (ext_Tm sigma_Val tau_Val Eq_Val s1)
        (ext_Tm (up_Val_Val sigma_Val) (up_Val_Val tau_Val)
           (upExt_Val_Val _ _ Eq_Val) s2)
  | prj _ s0 s1 =>
      congr_prj (eq_refl s0) (ext_Val sigma_Val tau_Val Eq_Val s1)
  | split _ s0 s1 =>
      congr_split (ext_Val sigma_Val tau_Val Eq_Val s0)
        (ext_Tm (up_Val_Val (up_Val_Val sigma_Val))
           (up_Val_Val (up_Val_Val tau_Val))
           (upExt_Val_Val _ _ (upExt_Val_Val _ _ Eq_Val)) s1)
  | case _ s0 s1 s2 =>
      congr_case (ext_Val sigma_Val tau_Val Eq_Val s0)
        (ext_Tm (up_Val_Val sigma_Val) (up_Val_Val tau_Val)
           (upExt_Val_Val _ _ Eq_Val) s1)
        (ext_Tm (up_Val_Val sigma_Val) (up_Val_Val tau_Val)
           (upExt_Val_Val _ _ Eq_Val) s2)
  | app _ s0 s1 =>
      congr_app (ext_Val sigma_Val tau_Val Eq_Val s0)
        (ext_Val sigma_Val tau_Val Eq_Val s1)
  | unfold _ s0 => congr_unfold (ext_Val sigma_Val tau_Val Eq_Val s0)
  | box _ s0 => congr_box (ext_Val sigma_Val tau_Val Eq_Val s0)
  | bind _ s0 s1 =>
      congr_bind (ext_Tm sigma_Val tau_Val Eq_Val s0)
        (ext_Tm (up_Val_Val sigma_Val) (up_Val_Val tau_Val)
           (upExt_Val_Val _ _ Eq_Val) s1)
  end.

Lemma up_ren_ren_Val_Val {k : nat} {l : nat} {m : nat} (xi : fin k -> fin l)
  (zeta : fin l -> fin m) (rho : fin k -> fin m)
  (Eq : forall x, funcomp zeta xi x = rho x) :
  forall x,
  funcomp (upRen_Val_Val zeta) (upRen_Val_Val xi) x = upRen_Val_Val rho x.
Proof.
exact (up_ren_ren xi zeta rho Eq).
Qed.

Lemma up_ren_ren_list_Val_Val {p : nat} {k : nat} {l : nat} {m : nat}
  (xi : fin k -> fin l) (zeta : fin l -> fin m) (rho : fin k -> fin m)
  (Eq : forall x, funcomp zeta xi x = rho x) :
  forall x,
  funcomp (upRen_list_Val_Val p zeta) (upRen_list_Val_Val p xi) x =
  upRen_list_Val_Val p rho x.
Proof.
exact (up_ren_ren_p Eq).
Qed.

Fixpoint compRenRen_Val {k_Val : nat} {l_Val : nat} {m_Val : nat}
(xi_Val : fin m_Val -> fin k_Val) (zeta_Val : fin k_Val -> fin l_Val)
(rho_Val : fin m_Val -> fin l_Val)
(Eq_Val : forall x, funcomp zeta_Val xi_Val x = rho_Val x) (s : Val m_Val)
{struct s} : ren_Val zeta_Val (ren_Val xi_Val s) = ren_Val rho_Val s :=
  match s with
  | var _ s0 => ap (var l_Val) (Eq_Val s0)
  | zero _ => congr_zero
  | succ _ s0 =>
      congr_succ (compRenRen_Val xi_Val zeta_Val rho_Val Eq_Val s0)
  | prod _ s0 s1 =>
      congr_prod (compRenRen_Val xi_Val zeta_Val rho_Val Eq_Val s0)
        (compRenRen_Val xi_Val zeta_Val rho_Val Eq_Val s1)
  | inj _ s0 s1 =>
      congr_inj (eq_refl s0)
        (compRenRen_Val xi_Val zeta_Val rho_Val Eq_Val s1)
  | abs _ s0 =>
      congr_abs
        (compRenRen_Tm (upRen_Val_Val xi_Val) (upRen_Val_Val zeta_Val)
           (upRen_Val_Val rho_Val) (up_ren_ren _ _ _ Eq_Val) s0)
  | rec _ s0 =>
      congr_rec
        (compRenRen_Val (upRen_Val_Val xi_Val) (upRen_Val_Val zeta_Val)
           (upRen_Val_Val rho_Val) (up_ren_ren _ _ _ Eq_Val) s0)
  | fold _ s0 =>
      congr_fold (compRenRen_Val xi_Val zeta_Val rho_Val Eq_Val s0)
  end
with compRenRen_Tm {k_Val : nat} {l_Val : nat} {m_Val : nat}
(xi_Val : fin m_Val -> fin k_Val) (zeta_Val : fin k_Val -> fin l_Val)
(rho_Val : fin m_Val -> fin l_Val)
(Eq_Val : forall x, funcomp zeta_Val xi_Val x = rho_Val x) (s : Tm m_Val)
{struct s} : ren_Tm zeta_Val (ren_Tm xi_Val s) = ren_Tm rho_Val s :=
  match s with
  | ret _ s0 => congr_ret (compRenRen_Val xi_Val zeta_Val rho_Val Eq_Val s0)
  | let_ _ s0 s1 =>
      congr_let_ (compRenRen_Tm xi_Val zeta_Val rho_Val Eq_Val s0)
        (compRenRen_Tm (upRen_Val_Val xi_Val) (upRen_Val_Val zeta_Val)
           (upRen_Val_Val rho_Val) (up_ren_ren _ _ _ Eq_Val) s1)
  | ifz _ s0 s1 s2 =>
      congr_ifz (compRenRen_Val xi_Val zeta_Val rho_Val Eq_Val s0)
        (compRenRen_Tm xi_Val zeta_Val rho_Val Eq_Val s1)
        (compRenRen_Tm (upRen_Val_Val xi_Val) (upRen_Val_Val zeta_Val)
           (upRen_Val_Val rho_Val) (up_ren_ren _ _ _ Eq_Val) s2)
  | prj _ s0 s1 =>
      congr_prj (eq_refl s0)
        (compRenRen_Val xi_Val zeta_Val rho_Val Eq_Val s1)
  | split _ s0 s1 =>
      congr_split (compRenRen_Val xi_Val zeta_Val rho_Val Eq_Val s0)
        (compRenRen_Tm (upRen_Val_Val (upRen_Val_Val xi_Val))
           (upRen_Val_Val (upRen_Val_Val zeta_Val))
           (upRen_Val_Val (upRen_Val_Val rho_Val))
           (up_ren_ren _ _ _ (up_ren_ren _ _ _ Eq_Val)) s1)
  | case _ s0 s1 s2 =>
      congr_case (compRenRen_Val xi_Val zeta_Val rho_Val Eq_Val s0)
        (compRenRen_Tm (upRen_Val_Val xi_Val) (upRen_Val_Val zeta_Val)
           (upRen_Val_Val rho_Val) (up_ren_ren _ _ _ Eq_Val) s1)
        (compRenRen_Tm (upRen_Val_Val xi_Val) (upRen_Val_Val zeta_Val)
           (upRen_Val_Val rho_Val) (up_ren_ren _ _ _ Eq_Val) s2)
  | app _ s0 s1 =>
      congr_app (compRenRen_Val xi_Val zeta_Val rho_Val Eq_Val s0)
        (compRenRen_Val xi_Val zeta_Val rho_Val Eq_Val s1)
  | unfold _ s0 =>
      congr_unfold (compRenRen_Val xi_Val zeta_Val rho_Val Eq_Val s0)
  | box _ s0 => congr_box (compRenRen_Val xi_Val zeta_Val rho_Val Eq_Val s0)
  | bind _ s0 s1 =>
      congr_bind (compRenRen_Tm xi_Val zeta_Val rho_Val Eq_Val s0)
        (compRenRen_Tm (upRen_Val_Val xi_Val) (upRen_Val_Val zeta_Val)
           (upRen_Val_Val rho_Val) (up_ren_ren _ _ _ Eq_Val) s1)
  end.

Lemma up_ren_subst_Val_Val {k : nat} {l : nat} {m_Val : nat}
  (xi : fin k -> fin l) (tau : fin l -> Val m_Val)
  (theta : fin k -> Val m_Val) (Eq : forall x, funcomp tau xi x = theta x) :
  forall x,
  funcomp (up_Val_Val tau) (upRen_Val_Val xi) x = up_Val_Val theta x.
Proof.
exact (fun n =>
       match n with
       | Some fin_n => ap (ren_Val shift) (Eq fin_n)
       | None => eq_refl
       end).
Qed.

Lemma up_ren_subst_list_Val_Val {p : nat} {k : nat} {l : nat} {m_Val : nat}
  (xi : fin k -> fin l) (tau : fin l -> Val m_Val)
  (theta : fin k -> Val m_Val) (Eq : forall x, funcomp tau xi x = theta x) :
  forall x,
  funcomp (up_list_Val_Val p tau) (upRen_list_Val_Val p xi) x =
  up_list_Val_Val p theta x.
Proof.
exact (fun n =>
       eq_trans (scons_p_comp' _ _ _ n)
         (scons_p_congr (fun z => scons_p_head' _ _ z)
            (fun z =>
             eq_trans (scons_p_tail' _ _ (xi z))
               (ap (ren_Val (shift_p p)) (Eq z))))).
Qed.

Fixpoint compRenSubst_Val {k_Val : nat} {l_Val : nat} {m_Val : nat}
(xi_Val : fin m_Val -> fin k_Val) (tau_Val : fin k_Val -> Val l_Val)
(theta_Val : fin m_Val -> Val l_Val)
(Eq_Val : forall x, funcomp tau_Val xi_Val x = theta_Val x) (s : Val m_Val)
{struct s} : subst_Val tau_Val (ren_Val xi_Val s) = subst_Val theta_Val s :=
  match s with
  | var _ s0 => Eq_Val s0
  | zero _ => congr_zero
  | succ _ s0 =>
      congr_succ (compRenSubst_Val xi_Val tau_Val theta_Val Eq_Val s0)
  | prod _ s0 s1 =>
      congr_prod (compRenSubst_Val xi_Val tau_Val theta_Val Eq_Val s0)
        (compRenSubst_Val xi_Val tau_Val theta_Val Eq_Val s1)
  | inj _ s0 s1 =>
      congr_inj (eq_refl s0)
        (compRenSubst_Val xi_Val tau_Val theta_Val Eq_Val s1)
  | abs _ s0 =>
      congr_abs
        (compRenSubst_Tm (upRen_Val_Val xi_Val) (up_Val_Val tau_Val)
           (up_Val_Val theta_Val) (up_ren_subst_Val_Val _ _ _ Eq_Val) s0)
  | rec _ s0 =>
      congr_rec
        (compRenSubst_Val (upRen_Val_Val xi_Val) (up_Val_Val tau_Val)
           (up_Val_Val theta_Val) (up_ren_subst_Val_Val _ _ _ Eq_Val) s0)
  | fold _ s0 =>
      congr_fold (compRenSubst_Val xi_Val tau_Val theta_Val Eq_Val s0)
  end
with compRenSubst_Tm {k_Val : nat} {l_Val : nat} {m_Val : nat}
(xi_Val : fin m_Val -> fin k_Val) (tau_Val : fin k_Val -> Val l_Val)
(theta_Val : fin m_Val -> Val l_Val)
(Eq_Val : forall x, funcomp tau_Val xi_Val x = theta_Val x) (s : Tm m_Val)
{struct s} : subst_Tm tau_Val (ren_Tm xi_Val s) = subst_Tm theta_Val s :=
  match s with
  | ret _ s0 =>
      congr_ret (compRenSubst_Val xi_Val tau_Val theta_Val Eq_Val s0)
  | let_ _ s0 s1 =>
      congr_let_ (compRenSubst_Tm xi_Val tau_Val theta_Val Eq_Val s0)
        (compRenSubst_Tm (upRen_Val_Val xi_Val) (up_Val_Val tau_Val)
           (up_Val_Val theta_Val) (up_ren_subst_Val_Val _ _ _ Eq_Val) s1)
  | ifz _ s0 s1 s2 =>
      congr_ifz (compRenSubst_Val xi_Val tau_Val theta_Val Eq_Val s0)
        (compRenSubst_Tm xi_Val tau_Val theta_Val Eq_Val s1)
        (compRenSubst_Tm (upRen_Val_Val xi_Val) (up_Val_Val tau_Val)
           (up_Val_Val theta_Val) (up_ren_subst_Val_Val _ _ _ Eq_Val) s2)
  | prj _ s0 s1 =>
      congr_prj (eq_refl s0)
        (compRenSubst_Val xi_Val tau_Val theta_Val Eq_Val s1)
  | split _ s0 s1 =>
      congr_split (compRenSubst_Val xi_Val tau_Val theta_Val Eq_Val s0)
        (compRenSubst_Tm (upRen_Val_Val (upRen_Val_Val xi_Val))
           (up_Val_Val (up_Val_Val tau_Val))
           (up_Val_Val (up_Val_Val theta_Val))
           (up_ren_subst_Val_Val _ _ _ (up_ren_subst_Val_Val _ _ _ Eq_Val))
           s1)
  | case _ s0 s1 s2 =>
      congr_case (compRenSubst_Val xi_Val tau_Val theta_Val Eq_Val s0)
        (compRenSubst_Tm (upRen_Val_Val xi_Val) (up_Val_Val tau_Val)
           (up_Val_Val theta_Val) (up_ren_subst_Val_Val _ _ _ Eq_Val) s1)
        (compRenSubst_Tm (upRen_Val_Val xi_Val) (up_Val_Val tau_Val)
           (up_Val_Val theta_Val) (up_ren_subst_Val_Val _ _ _ Eq_Val) s2)
  | app _ s0 s1 =>
      congr_app (compRenSubst_Val xi_Val tau_Val theta_Val Eq_Val s0)
        (compRenSubst_Val xi_Val tau_Val theta_Val Eq_Val s1)
  | unfold _ s0 =>
      congr_unfold (compRenSubst_Val xi_Val tau_Val theta_Val Eq_Val s0)
  | box _ s0 =>
      congr_box (compRenSubst_Val xi_Val tau_Val theta_Val Eq_Val s0)
  | bind _ s0 s1 =>
      congr_bind (compRenSubst_Tm xi_Val tau_Val theta_Val Eq_Val s0)
        (compRenSubst_Tm (upRen_Val_Val xi_Val) (up_Val_Val tau_Val)
           (up_Val_Val theta_Val) (up_ren_subst_Val_Val _ _ _ Eq_Val) s1)
  end.

Lemma up_subst_ren_Val_Val {k : nat} {l_Val : nat} {m_Val : nat}
  (sigma : fin k -> Val l_Val) (zeta_Val : fin l_Val -> fin m_Val)
  (theta : fin k -> Val m_Val)
  (Eq : forall x, funcomp (ren_Val zeta_Val) sigma x = theta x) :
  forall x,
  funcomp (ren_Val (upRen_Val_Val zeta_Val)) (up_Val_Val sigma) x =
  up_Val_Val theta x.
Proof.
exact (fun n =>
       match n with
       | Some fin_n =>
           eq_trans
             (compRenRen_Val shift (upRen_Val_Val zeta_Val)
                (funcomp shift zeta_Val) (fun x => eq_refl) (sigma fin_n))
             (eq_trans
                (eq_sym
                   (compRenRen_Val zeta_Val shift (funcomp shift zeta_Val)
                      (fun x => eq_refl) (sigma fin_n)))
                (ap (ren_Val shift) (Eq fin_n)))
       | None => eq_refl
       end).
Qed.

Lemma up_subst_ren_list_Val_Val {p : nat} {k : nat} {l_Val : nat}
  {m_Val : nat} (sigma : fin k -> Val l_Val)
  (zeta_Val : fin l_Val -> fin m_Val) (theta : fin k -> Val m_Val)
  (Eq : forall x, funcomp (ren_Val zeta_Val) sigma x = theta x) :
  forall x,
  funcomp (ren_Val (upRen_list_Val_Val p zeta_Val)) (up_list_Val_Val p sigma)
    x =
  up_list_Val_Val p theta x.
Proof.
exact (fun n =>
       eq_trans (scons_p_comp' _ _ _ n)
         (scons_p_congr
            (fun x => ap (var (plus p m_Val)) (scons_p_head' _ _ x))
            (fun n =>
             eq_trans
               (compRenRen_Val (shift_p p) (upRen_list_Val_Val p zeta_Val)
                  (funcomp (shift_p p) zeta_Val)
                  (fun x => scons_p_tail' _ _ x) (sigma n))
               (eq_trans
                  (eq_sym
                     (compRenRen_Val zeta_Val (shift_p p)
                        (funcomp (shift_p p) zeta_Val) (fun x => eq_refl)
                        (sigma n)))
                  (ap (ren_Val (shift_p p)) (Eq n)))))).
Qed.

Fixpoint compSubstRen_Val {k_Val : nat} {l_Val : nat} {m_Val : nat}
(sigma_Val : fin m_Val -> Val k_Val) (zeta_Val : fin k_Val -> fin l_Val)
(theta_Val : fin m_Val -> Val l_Val)
(Eq_Val : forall x, funcomp (ren_Val zeta_Val) sigma_Val x = theta_Val x)
(s : Val m_Val) {struct s} :
ren_Val zeta_Val (subst_Val sigma_Val s) = subst_Val theta_Val s :=
  match s with
  | var _ s0 => Eq_Val s0
  | zero _ => congr_zero
  | succ _ s0 =>
      congr_succ (compSubstRen_Val sigma_Val zeta_Val theta_Val Eq_Val s0)
  | prod _ s0 s1 =>
      congr_prod (compSubstRen_Val sigma_Val zeta_Val theta_Val Eq_Val s0)
        (compSubstRen_Val sigma_Val zeta_Val theta_Val Eq_Val s1)
  | inj _ s0 s1 =>
      congr_inj (eq_refl s0)
        (compSubstRen_Val sigma_Val zeta_Val theta_Val Eq_Val s1)
  | abs _ s0 =>
      congr_abs
        (compSubstRen_Tm (up_Val_Val sigma_Val) (upRen_Val_Val zeta_Val)
           (up_Val_Val theta_Val) (up_subst_ren_Val_Val _ _ _ Eq_Val) s0)
  | rec _ s0 =>
      congr_rec
        (compSubstRen_Val (up_Val_Val sigma_Val) (upRen_Val_Val zeta_Val)
           (up_Val_Val theta_Val) (up_subst_ren_Val_Val _ _ _ Eq_Val) s0)
  | fold _ s0 =>
      congr_fold (compSubstRen_Val sigma_Val zeta_Val theta_Val Eq_Val s0)
  end
with compSubstRen_Tm {k_Val : nat} {l_Val : nat} {m_Val : nat}
(sigma_Val : fin m_Val -> Val k_Val) (zeta_Val : fin k_Val -> fin l_Val)
(theta_Val : fin m_Val -> Val l_Val)
(Eq_Val : forall x, funcomp (ren_Val zeta_Val) sigma_Val x = theta_Val x)
(s : Tm m_Val) {struct s} :
ren_Tm zeta_Val (subst_Tm sigma_Val s) = subst_Tm theta_Val s :=
  match s with
  | ret _ s0 =>
      congr_ret (compSubstRen_Val sigma_Val zeta_Val theta_Val Eq_Val s0)
  | let_ _ s0 s1 =>
      congr_let_ (compSubstRen_Tm sigma_Val zeta_Val theta_Val Eq_Val s0)
        (compSubstRen_Tm (up_Val_Val sigma_Val) (upRen_Val_Val zeta_Val)
           (up_Val_Val theta_Val) (up_subst_ren_Val_Val _ _ _ Eq_Val) s1)
  | ifz _ s0 s1 s2 =>
      congr_ifz (compSubstRen_Val sigma_Val zeta_Val theta_Val Eq_Val s0)
        (compSubstRen_Tm sigma_Val zeta_Val theta_Val Eq_Val s1)
        (compSubstRen_Tm (up_Val_Val sigma_Val) (upRen_Val_Val zeta_Val)
           (up_Val_Val theta_Val) (up_subst_ren_Val_Val _ _ _ Eq_Val) s2)
  | prj _ s0 s1 =>
      congr_prj (eq_refl s0)
        (compSubstRen_Val sigma_Val zeta_Val theta_Val Eq_Val s1)
  | split _ s0 s1 =>
      congr_split (compSubstRen_Val sigma_Val zeta_Val theta_Val Eq_Val s0)
        (compSubstRen_Tm (up_Val_Val (up_Val_Val sigma_Val))
           (upRen_Val_Val (upRen_Val_Val zeta_Val))
           (up_Val_Val (up_Val_Val theta_Val))
           (up_subst_ren_Val_Val _ _ _ (up_subst_ren_Val_Val _ _ _ Eq_Val))
           s1)
  | case _ s0 s1 s2 =>
      congr_case (compSubstRen_Val sigma_Val zeta_Val theta_Val Eq_Val s0)
        (compSubstRen_Tm (up_Val_Val sigma_Val) (upRen_Val_Val zeta_Val)
           (up_Val_Val theta_Val) (up_subst_ren_Val_Val _ _ _ Eq_Val) s1)
        (compSubstRen_Tm (up_Val_Val sigma_Val) (upRen_Val_Val zeta_Val)
           (up_Val_Val theta_Val) (up_subst_ren_Val_Val _ _ _ Eq_Val) s2)
  | app _ s0 s1 =>
      congr_app (compSubstRen_Val sigma_Val zeta_Val theta_Val Eq_Val s0)
        (compSubstRen_Val sigma_Val zeta_Val theta_Val Eq_Val s1)
  | unfold _ s0 =>
      congr_unfold (compSubstRen_Val sigma_Val zeta_Val theta_Val Eq_Val s0)
  | box _ s0 =>
      congr_box (compSubstRen_Val sigma_Val zeta_Val theta_Val Eq_Val s0)
  | bind _ s0 s1 =>
      congr_bind (compSubstRen_Tm sigma_Val zeta_Val theta_Val Eq_Val s0)
        (compSubstRen_Tm (up_Val_Val sigma_Val) (upRen_Val_Val zeta_Val)
           (up_Val_Val theta_Val) (up_subst_ren_Val_Val _ _ _ Eq_Val) s1)
  end.

Lemma up_subst_subst_Val_Val {k : nat} {l_Val : nat} {m_Val : nat}
  (sigma : fin k -> Val l_Val) (tau_Val : fin l_Val -> Val m_Val)
  (theta : fin k -> Val m_Val)
  (Eq : forall x, funcomp (subst_Val tau_Val) sigma x = theta x) :
  forall x,
  funcomp (subst_Val (up_Val_Val tau_Val)) (up_Val_Val sigma) x =
  up_Val_Val theta x.
Proof.
exact (fun n =>
       match n with
       | Some fin_n =>
           eq_trans
             (compRenSubst_Val shift (up_Val_Val tau_Val)
                (funcomp (up_Val_Val tau_Val) shift) (fun x => eq_refl)
                (sigma fin_n))
             (eq_trans
                (eq_sym
                   (compSubstRen_Val tau_Val shift
                      (funcomp (ren_Val shift) tau_Val) (fun x => eq_refl)
                      (sigma fin_n)))
                (ap (ren_Val shift) (Eq fin_n)))
       | None => eq_refl
       end).
Qed.

Lemma up_subst_subst_list_Val_Val {p : nat} {k : nat} {l_Val : nat}
  {m_Val : nat} (sigma : fin k -> Val l_Val)
  (tau_Val : fin l_Val -> Val m_Val) (theta : fin k -> Val m_Val)
  (Eq : forall x, funcomp (subst_Val tau_Val) sigma x = theta x) :
  forall x,
  funcomp (subst_Val (up_list_Val_Val p tau_Val)) (up_list_Val_Val p sigma) x =
  up_list_Val_Val p theta x.
Proof.
exact (fun n =>
       eq_trans
         (scons_p_comp' (funcomp (var (plus p l_Val)) (zero_p p)) _ _ n)
         (scons_p_congr
            (fun x => scons_p_head' _ (fun z => ren_Val (shift_p p) _) x)
            (fun n =>
             eq_trans
               (compRenSubst_Val (shift_p p) (up_list_Val_Val p tau_Val)
                  (funcomp (up_list_Val_Val p tau_Val) (shift_p p))
                  (fun x => eq_refl) (sigma n))
               (eq_trans
                  (eq_sym
                     (compSubstRen_Val tau_Val (shift_p p) _
                        (fun x => eq_sym (scons_p_tail' _ _ x)) (sigma n)))
                  (ap (ren_Val (shift_p p)) (Eq n)))))).
Qed.

Fixpoint compSubstSubst_Val {k_Val : nat} {l_Val : nat} {m_Val : nat}
(sigma_Val : fin m_Val -> Val k_Val) (tau_Val : fin k_Val -> Val l_Val)
(theta_Val : fin m_Val -> Val l_Val)
(Eq_Val : forall x, funcomp (subst_Val tau_Val) sigma_Val x = theta_Val x)
(s : Val m_Val) {struct s} :
subst_Val tau_Val (subst_Val sigma_Val s) = subst_Val theta_Val s :=
  match s with
  | var _ s0 => Eq_Val s0
  | zero _ => congr_zero
  | succ _ s0 =>
      congr_succ (compSubstSubst_Val sigma_Val tau_Val theta_Val Eq_Val s0)
  | prod _ s0 s1 =>
      congr_prod (compSubstSubst_Val sigma_Val tau_Val theta_Val Eq_Val s0)
        (compSubstSubst_Val sigma_Val tau_Val theta_Val Eq_Val s1)
  | inj _ s0 s1 =>
      congr_inj (eq_refl s0)
        (compSubstSubst_Val sigma_Val tau_Val theta_Val Eq_Val s1)
  | abs _ s0 =>
      congr_abs
        (compSubstSubst_Tm (up_Val_Val sigma_Val) (up_Val_Val tau_Val)
           (up_Val_Val theta_Val) (up_subst_subst_Val_Val _ _ _ Eq_Val) s0)
  | rec _ s0 =>
      congr_rec
        (compSubstSubst_Val (up_Val_Val sigma_Val) (up_Val_Val tau_Val)
           (up_Val_Val theta_Val) (up_subst_subst_Val_Val _ _ _ Eq_Val) s0)
  | fold _ s0 =>
      congr_fold (compSubstSubst_Val sigma_Val tau_Val theta_Val Eq_Val s0)
  end
with compSubstSubst_Tm {k_Val : nat} {l_Val : nat} {m_Val : nat}
(sigma_Val : fin m_Val -> Val k_Val) (tau_Val : fin k_Val -> Val l_Val)
(theta_Val : fin m_Val -> Val l_Val)
(Eq_Val : forall x, funcomp (subst_Val tau_Val) sigma_Val x = theta_Val x)
(s : Tm m_Val) {struct s} :
subst_Tm tau_Val (subst_Tm sigma_Val s) = subst_Tm theta_Val s :=
  match s with
  | ret _ s0 =>
      congr_ret (compSubstSubst_Val sigma_Val tau_Val theta_Val Eq_Val s0)
  | let_ _ s0 s1 =>
      congr_let_ (compSubstSubst_Tm sigma_Val tau_Val theta_Val Eq_Val s0)
        (compSubstSubst_Tm (up_Val_Val sigma_Val) (up_Val_Val tau_Val)
           (up_Val_Val theta_Val) (up_subst_subst_Val_Val _ _ _ Eq_Val) s1)
  | ifz _ s0 s1 s2 =>
      congr_ifz (compSubstSubst_Val sigma_Val tau_Val theta_Val Eq_Val s0)
        (compSubstSubst_Tm sigma_Val tau_Val theta_Val Eq_Val s1)
        (compSubstSubst_Tm (up_Val_Val sigma_Val) (up_Val_Val tau_Val)
           (up_Val_Val theta_Val) (up_subst_subst_Val_Val _ _ _ Eq_Val) s2)
  | prj _ s0 s1 =>
      congr_prj (eq_refl s0)
        (compSubstSubst_Val sigma_Val tau_Val theta_Val Eq_Val s1)
  | split _ s0 s1 =>
      congr_split (compSubstSubst_Val sigma_Val tau_Val theta_Val Eq_Val s0)
        (compSubstSubst_Tm (up_Val_Val (up_Val_Val sigma_Val))
           (up_Val_Val (up_Val_Val tau_Val))
           (up_Val_Val (up_Val_Val theta_Val))
           (up_subst_subst_Val_Val _ _ _
              (up_subst_subst_Val_Val _ _ _ Eq_Val))
           s1)
  | case _ s0 s1 s2 =>
      congr_case (compSubstSubst_Val sigma_Val tau_Val theta_Val Eq_Val s0)
        (compSubstSubst_Tm (up_Val_Val sigma_Val) (up_Val_Val tau_Val)
           (up_Val_Val theta_Val) (up_subst_subst_Val_Val _ _ _ Eq_Val) s1)
        (compSubstSubst_Tm (up_Val_Val sigma_Val) (up_Val_Val tau_Val)
           (up_Val_Val theta_Val) (up_subst_subst_Val_Val _ _ _ Eq_Val) s2)
  | app _ s0 s1 =>
      congr_app (compSubstSubst_Val sigma_Val tau_Val theta_Val Eq_Val s0)
        (compSubstSubst_Val sigma_Val tau_Val theta_Val Eq_Val s1)
  | unfold _ s0 =>
      congr_unfold (compSubstSubst_Val sigma_Val tau_Val theta_Val Eq_Val s0)
  | box _ s0 =>
      congr_box (compSubstSubst_Val sigma_Val tau_Val theta_Val Eq_Val s0)
  | bind _ s0 s1 =>
      congr_bind (compSubstSubst_Tm sigma_Val tau_Val theta_Val Eq_Val s0)
        (compSubstSubst_Tm (up_Val_Val sigma_Val) (up_Val_Val tau_Val)
           (up_Val_Val theta_Val) (up_subst_subst_Val_Val _ _ _ Eq_Val) s1)
  end.

Lemma renRen_Val {k_Val : nat} {l_Val : nat} {m_Val : nat}
  (xi_Val : fin m_Val -> fin k_Val) (zeta_Val : fin k_Val -> fin l_Val)
  (s : Val m_Val) :
  ren_Val zeta_Val (ren_Val xi_Val s) = ren_Val (funcomp zeta_Val xi_Val) s.
Proof.
exact (compRenRen_Val xi_Val zeta_Val _ (fun n => eq_refl) s).
Qed.

Lemma renRen'_Val_pointwise {k_Val : nat} {l_Val : nat} {m_Val : nat}
  (xi_Val : fin m_Val -> fin k_Val) (zeta_Val : fin k_Val -> fin l_Val) :
  pointwise_relation _ eq (funcomp (ren_Val zeta_Val) (ren_Val xi_Val))
    (ren_Val (funcomp zeta_Val xi_Val)).
Proof.
exact (fun s => compRenRen_Val xi_Val zeta_Val _ (fun n => eq_refl) s).
Qed.

Lemma renRen_Tm {k_Val : nat} {l_Val : nat} {m_Val : nat}
  (xi_Val : fin m_Val -> fin k_Val) (zeta_Val : fin k_Val -> fin l_Val)
  (s : Tm m_Val) :
  ren_Tm zeta_Val (ren_Tm xi_Val s) = ren_Tm (funcomp zeta_Val xi_Val) s.
Proof.
exact (compRenRen_Tm xi_Val zeta_Val _ (fun n => eq_refl) s).
Qed.

Lemma renRen'_Tm_pointwise {k_Val : nat} {l_Val : nat} {m_Val : nat}
  (xi_Val : fin m_Val -> fin k_Val) (zeta_Val : fin k_Val -> fin l_Val) :
  pointwise_relation _ eq (funcomp (ren_Tm zeta_Val) (ren_Tm xi_Val))
    (ren_Tm (funcomp zeta_Val xi_Val)).
Proof.
exact (fun s => compRenRen_Tm xi_Val zeta_Val _ (fun n => eq_refl) s).
Qed.

Lemma renSubst_Val {k_Val : nat} {l_Val : nat} {m_Val : nat}
  (xi_Val : fin m_Val -> fin k_Val) (tau_Val : fin k_Val -> Val l_Val)
  (s : Val m_Val) :
  subst_Val tau_Val (ren_Val xi_Val s) = subst_Val (funcomp tau_Val xi_Val) s.
Proof.
exact (compRenSubst_Val xi_Val tau_Val _ (fun n => eq_refl) s).
Qed.

Lemma renSubst_Val_pointwise {k_Val : nat} {l_Val : nat} {m_Val : nat}
  (xi_Val : fin m_Val -> fin k_Val) (tau_Val : fin k_Val -> Val l_Val) :
  pointwise_relation _ eq (funcomp (subst_Val tau_Val) (ren_Val xi_Val))
    (subst_Val (funcomp tau_Val xi_Val)).
Proof.
exact (fun s => compRenSubst_Val xi_Val tau_Val _ (fun n => eq_refl) s).
Qed.

Lemma renSubst_Tm {k_Val : nat} {l_Val : nat} {m_Val : nat}
  (xi_Val : fin m_Val -> fin k_Val) (tau_Val : fin k_Val -> Val l_Val)
  (s : Tm m_Val) :
  subst_Tm tau_Val (ren_Tm xi_Val s) = subst_Tm (funcomp tau_Val xi_Val) s.
Proof.
exact (compRenSubst_Tm xi_Val tau_Val _ (fun n => eq_refl) s).
Qed.

Lemma renSubst_Tm_pointwise {k_Val : nat} {l_Val : nat} {m_Val : nat}
  (xi_Val : fin m_Val -> fin k_Val) (tau_Val : fin k_Val -> Val l_Val) :
  pointwise_relation _ eq (funcomp (subst_Tm tau_Val) (ren_Tm xi_Val))
    (subst_Tm (funcomp tau_Val xi_Val)).
Proof.
exact (fun s => compRenSubst_Tm xi_Val tau_Val _ (fun n => eq_refl) s).
Qed.

Lemma substRen_Val {k_Val : nat} {l_Val : nat} {m_Val : nat}
  (sigma_Val : fin m_Val -> Val k_Val) (zeta_Val : fin k_Val -> fin l_Val)
  (s : Val m_Val) :
  ren_Val zeta_Val (subst_Val sigma_Val s) =
  subst_Val (funcomp (ren_Val zeta_Val) sigma_Val) s.
Proof.
exact (compSubstRen_Val sigma_Val zeta_Val _ (fun n => eq_refl) s).
Qed.

Lemma substRen_Val_pointwise {k_Val : nat} {l_Val : nat} {m_Val : nat}
  (sigma_Val : fin m_Val -> Val k_Val) (zeta_Val : fin k_Val -> fin l_Val) :
  pointwise_relation _ eq (funcomp (ren_Val zeta_Val) (subst_Val sigma_Val))
    (subst_Val (funcomp (ren_Val zeta_Val) sigma_Val)).
Proof.
exact (fun s => compSubstRen_Val sigma_Val zeta_Val _ (fun n => eq_refl) s).
Qed.

Lemma substRen_Tm {k_Val : nat} {l_Val : nat} {m_Val : nat}
  (sigma_Val : fin m_Val -> Val k_Val) (zeta_Val : fin k_Val -> fin l_Val)
  (s : Tm m_Val) :
  ren_Tm zeta_Val (subst_Tm sigma_Val s) =
  subst_Tm (funcomp (ren_Val zeta_Val) sigma_Val) s.
Proof.
exact (compSubstRen_Tm sigma_Val zeta_Val _ (fun n => eq_refl) s).
Qed.

Lemma substRen_Tm_pointwise {k_Val : nat} {l_Val : nat} {m_Val : nat}
  (sigma_Val : fin m_Val -> Val k_Val) (zeta_Val : fin k_Val -> fin l_Val) :
  pointwise_relation _ eq (funcomp (ren_Tm zeta_Val) (subst_Tm sigma_Val))
    (subst_Tm (funcomp (ren_Val zeta_Val) sigma_Val)).
Proof.
exact (fun s => compSubstRen_Tm sigma_Val zeta_Val _ (fun n => eq_refl) s).
Qed.

Lemma substSubst_Val {k_Val : nat} {l_Val : nat} {m_Val : nat}
  (sigma_Val : fin m_Val -> Val k_Val) (tau_Val : fin k_Val -> Val l_Val)
  (s : Val m_Val) :
  subst_Val tau_Val (subst_Val sigma_Val s) =
  subst_Val (funcomp (subst_Val tau_Val) sigma_Val) s.
Proof.
exact (compSubstSubst_Val sigma_Val tau_Val _ (fun n => eq_refl) s).
Qed.

Lemma substSubst_Val_pointwise {k_Val : nat} {l_Val : nat} {m_Val : nat}
  (sigma_Val : fin m_Val -> Val k_Val) (tau_Val : fin k_Val -> Val l_Val) :
  pointwise_relation _ eq (funcomp (subst_Val tau_Val) (subst_Val sigma_Val))
    (subst_Val (funcomp (subst_Val tau_Val) sigma_Val)).
Proof.
exact (fun s => compSubstSubst_Val sigma_Val tau_Val _ (fun n => eq_refl) s).
Qed.

Lemma substSubst_Tm {k_Val : nat} {l_Val : nat} {m_Val : nat}
  (sigma_Val : fin m_Val -> Val k_Val) (tau_Val : fin k_Val -> Val l_Val)
  (s : Tm m_Val) :
  subst_Tm tau_Val (subst_Tm sigma_Val s) =
  subst_Tm (funcomp (subst_Val tau_Val) sigma_Val) s.
Proof.
exact (compSubstSubst_Tm sigma_Val tau_Val _ (fun n => eq_refl) s).
Qed.

Lemma substSubst_Tm_pointwise {k_Val : nat} {l_Val : nat} {m_Val : nat}
  (sigma_Val : fin m_Val -> Val k_Val) (tau_Val : fin k_Val -> Val l_Val) :
  pointwise_relation _ eq (funcomp (subst_Tm tau_Val) (subst_Tm sigma_Val))
    (subst_Tm (funcomp (subst_Val tau_Val) sigma_Val)).
Proof.
exact (fun s => compSubstSubst_Tm sigma_Val tau_Val _ (fun n => eq_refl) s).
Qed.

Lemma rinstInst_up_Val_Val {m : nat} {n_Val : nat} (xi : fin m -> fin n_Val)
  (sigma : fin m -> Val n_Val)
  (Eq : forall x, funcomp (var n_Val) xi x = sigma x) :
  forall x, funcomp (var (S n_Val)) (upRen_Val_Val xi) x = up_Val_Val sigma x.
Proof.
exact (fun n =>
       match n with
       | Some fin_n => ap (ren_Val shift) (Eq fin_n)
       | None => eq_refl
       end).
Qed.

Lemma rinstInst_up_list_Val_Val {p : nat} {m : nat} {n_Val : nat}
  (xi : fin m -> fin n_Val) (sigma : fin m -> Val n_Val)
  (Eq : forall x, funcomp (var n_Val) xi x = sigma x) :
  forall x,
  funcomp (var (plus p n_Val)) (upRen_list_Val_Val p xi) x =
  up_list_Val_Val p sigma x.
Proof.
exact (fun n =>
       eq_trans (scons_p_comp' _ _ (var (plus p n_Val)) n)
         (scons_p_congr (fun z => eq_refl)
            (fun n => ap (ren_Val (shift_p p)) (Eq n)))).
Qed.

Fixpoint rinst_inst_Val {m_Val : nat} {n_Val : nat}
(xi_Val : fin m_Val -> fin n_Val) (sigma_Val : fin m_Val -> Val n_Val)
(Eq_Val : forall x, funcomp (var n_Val) xi_Val x = sigma_Val x)
(s : Val m_Val) {struct s} : ren_Val xi_Val s = subst_Val sigma_Val s :=
  match s with
  | var _ s0 => Eq_Val s0
  | zero _ => congr_zero
  | succ _ s0 => congr_succ (rinst_inst_Val xi_Val sigma_Val Eq_Val s0)
  | prod _ s0 s1 =>
      congr_prod (rinst_inst_Val xi_Val sigma_Val Eq_Val s0)
        (rinst_inst_Val xi_Val sigma_Val Eq_Val s1)
  | inj _ s0 s1 =>
      congr_inj (eq_refl s0) (rinst_inst_Val xi_Val sigma_Val Eq_Val s1)
  | abs _ s0 =>
      congr_abs
        (rinst_inst_Tm (upRen_Val_Val xi_Val) (up_Val_Val sigma_Val)
           (rinstInst_up_Val_Val _ _ Eq_Val) s0)
  | rec _ s0 =>
      congr_rec
        (rinst_inst_Val (upRen_Val_Val xi_Val) (up_Val_Val sigma_Val)
           (rinstInst_up_Val_Val _ _ Eq_Val) s0)
  | fold _ s0 => congr_fold (rinst_inst_Val xi_Val sigma_Val Eq_Val s0)
  end
with rinst_inst_Tm {m_Val : nat} {n_Val : nat}
(xi_Val : fin m_Val -> fin n_Val) (sigma_Val : fin m_Val -> Val n_Val)
(Eq_Val : forall x, funcomp (var n_Val) xi_Val x = sigma_Val x)
(s : Tm m_Val) {struct s} : ren_Tm xi_Val s = subst_Tm sigma_Val s :=
  match s with
  | ret _ s0 => congr_ret (rinst_inst_Val xi_Val sigma_Val Eq_Val s0)
  | let_ _ s0 s1 =>
      congr_let_ (rinst_inst_Tm xi_Val sigma_Val Eq_Val s0)
        (rinst_inst_Tm (upRen_Val_Val xi_Val) (up_Val_Val sigma_Val)
           (rinstInst_up_Val_Val _ _ Eq_Val) s1)
  | ifz _ s0 s1 s2 =>
      congr_ifz (rinst_inst_Val xi_Val sigma_Val Eq_Val s0)
        (rinst_inst_Tm xi_Val sigma_Val Eq_Val s1)
        (rinst_inst_Tm (upRen_Val_Val xi_Val) (up_Val_Val sigma_Val)
           (rinstInst_up_Val_Val _ _ Eq_Val) s2)
  | prj _ s0 s1 =>
      congr_prj (eq_refl s0) (rinst_inst_Val xi_Val sigma_Val Eq_Val s1)
  | split _ s0 s1 =>
      congr_split (rinst_inst_Val xi_Val sigma_Val Eq_Val s0)
        (rinst_inst_Tm (upRen_Val_Val (upRen_Val_Val xi_Val))
           (up_Val_Val (up_Val_Val sigma_Val))
           (rinstInst_up_Val_Val _ _ (rinstInst_up_Val_Val _ _ Eq_Val)) s1)
  | case _ s0 s1 s2 =>
      congr_case (rinst_inst_Val xi_Val sigma_Val Eq_Val s0)
        (rinst_inst_Tm (upRen_Val_Val xi_Val) (up_Val_Val sigma_Val)
           (rinstInst_up_Val_Val _ _ Eq_Val) s1)
        (rinst_inst_Tm (upRen_Val_Val xi_Val) (up_Val_Val sigma_Val)
           (rinstInst_up_Val_Val _ _ Eq_Val) s2)
  | app _ s0 s1 =>
      congr_app (rinst_inst_Val xi_Val sigma_Val Eq_Val s0)
        (rinst_inst_Val xi_Val sigma_Val Eq_Val s1)
  | unfold _ s0 => congr_unfold (rinst_inst_Val xi_Val sigma_Val Eq_Val s0)
  | box _ s0 => congr_box (rinst_inst_Val xi_Val sigma_Val Eq_Val s0)
  | bind _ s0 s1 =>
      congr_bind (rinst_inst_Tm xi_Val sigma_Val Eq_Val s0)
        (rinst_inst_Tm (upRen_Val_Val xi_Val) (up_Val_Val sigma_Val)
           (rinstInst_up_Val_Val _ _ Eq_Val) s1)
  end.

Lemma rinstInst'_Val {m_Val : nat} {n_Val : nat}
  (xi_Val : fin m_Val -> fin n_Val) (s : Val m_Val) :
  ren_Val xi_Val s = subst_Val (funcomp (var n_Val) xi_Val) s.
Proof.
exact (rinst_inst_Val xi_Val _ (fun n => eq_refl) s).
Qed.

Lemma rinstInst'_Val_pointwise {m_Val : nat} {n_Val : nat}
  (xi_Val : fin m_Val -> fin n_Val) :
  pointwise_relation _ eq (ren_Val xi_Val)
    (subst_Val (funcomp (var n_Val) xi_Val)).
Proof.
exact (fun s => rinst_inst_Val xi_Val _ (fun n => eq_refl) s).
Qed.

Lemma rinstInst'_Tm {m_Val : nat} {n_Val : nat}
  (xi_Val : fin m_Val -> fin n_Val) (s : Tm m_Val) :
  ren_Tm xi_Val s = subst_Tm (funcomp (var n_Val) xi_Val) s.
Proof.
exact (rinst_inst_Tm xi_Val _ (fun n => eq_refl) s).
Qed.

Lemma rinstInst'_Tm_pointwise {m_Val : nat} {n_Val : nat}
  (xi_Val : fin m_Val -> fin n_Val) :
  pointwise_relation _ eq (ren_Tm xi_Val)
    (subst_Tm (funcomp (var n_Val) xi_Val)).
Proof.
exact (fun s => rinst_inst_Tm xi_Val _ (fun n => eq_refl) s).
Qed.

Lemma instId'_Val {m_Val : nat} (s : Val m_Val) : subst_Val (var m_Val) s = s.
Proof.
exact (idSubst_Val (var m_Val) (fun n => eq_refl) s).
Qed.

Lemma instId'_Val_pointwise {m_Val : nat} :
  pointwise_relation _ eq (subst_Val (var m_Val)) id.
Proof.
exact (fun s => idSubst_Val (var m_Val) (fun n => eq_refl) s).
Qed.

Lemma instId'_Tm {m_Val : nat} (s : Tm m_Val) : subst_Tm (var m_Val) s = s.
Proof.
exact (idSubst_Tm (var m_Val) (fun n => eq_refl) s).
Qed.

Lemma instId'_Tm_pointwise {m_Val : nat} :
  pointwise_relation _ eq (subst_Tm (var m_Val)) id.
Proof.
exact (fun s => idSubst_Tm (var m_Val) (fun n => eq_refl) s).
Qed.

Lemma rinstId'_Val {m_Val : nat} (s : Val m_Val) : ren_Val id s = s.
Proof.
exact (eq_ind_r (fun t => t = s) (instId'_Val s) (rinstInst'_Val id s)).
Qed.

Lemma rinstId'_Val_pointwise {m_Val : nat} :
  pointwise_relation _ eq (@ren_Val m_Val m_Val id) id.
Proof.
exact (fun s =>
       eq_ind_r (fun t => t = s) (instId'_Val s) (rinstInst'_Val id s)).
Qed.

Lemma rinstId'_Tm {m_Val : nat} (s : Tm m_Val) : ren_Tm id s = s.
Proof.
exact (eq_ind_r (fun t => t = s) (instId'_Tm s) (rinstInst'_Tm id s)).
Qed.

Lemma rinstId'_Tm_pointwise {m_Val : nat} :
  pointwise_relation _ eq (@ren_Tm m_Val m_Val id) id.
Proof.
exact (fun s => eq_ind_r (fun t => t = s) (instId'_Tm s) (rinstInst'_Tm id s)).
Qed.

Lemma varL'_Val {m_Val : nat} {n_Val : nat}
  (sigma_Val : fin m_Val -> Val n_Val) (x : fin m_Val) :
  subst_Val sigma_Val (var m_Val x) = sigma_Val x.
Proof.
exact (eq_refl).
Qed.

Lemma varL'_Val_pointwise {m_Val : nat} {n_Val : nat}
  (sigma_Val : fin m_Val -> Val n_Val) :
  pointwise_relation _ eq (funcomp (subst_Val sigma_Val) (var m_Val))
    sigma_Val.
Proof.
exact (fun x => eq_refl).
Qed.

Lemma varLRen'_Val {m_Val : nat} {n_Val : nat}
  (xi_Val : fin m_Val -> fin n_Val) (x : fin m_Val) :
  ren_Val xi_Val (var m_Val x) = var n_Val (xi_Val x).
Proof.
exact (eq_refl).
Qed.

Lemma varLRen'_Val_pointwise {m_Val : nat} {n_Val : nat}
  (xi_Val : fin m_Val -> fin n_Val) :
  pointwise_relation _ eq (funcomp (ren_Val xi_Val) (var m_Val))
    (funcomp (var n_Val) xi_Val).
Proof.
exact (fun x => eq_refl).
Qed.

Class Up_Tm X Y :=
    up_Tm : X -> Y.

Class Up_Val X Y :=
    up_Val : X -> Y.

#[global]
Instance Subst_Tm  {m_Val n_Val : nat}: (Subst1 _ _ _) :=
 (@subst_Tm m_Val n_Val).

#[global]
Instance Subst_Val  {m_Val n_Val : nat}: (Subst1 _ _ _) :=
 (@subst_Val m_Val n_Val).

#[global]
Instance Up_Val_Val  {m n_Val : nat}: (Up_Val _ _) := (@up_Val_Val m n_Val).

#[global]
Instance Ren_Tm  {m_Val n_Val : nat}: (Ren1 _ _ _) := (@ren_Tm m_Val n_Val).

#[global]
Instance Ren_Val  {m_Val n_Val : nat}: (Ren1 _ _ _) := (@ren_Val m_Val n_Val).

#[global]
Instance VarInstance_Val  {n_Val : nat}: (Var _ _) := (@var n_Val).

Notation "s [ sigma_Val ]" := (subst_Tm sigma_Val s)
( at level 7, left associativity, only printing)  : subst_scope.

Notation "↑__Tm" := up_Tm (only printing)  : subst_scope.

Notation "s [ sigma_Val ]" := (subst_Val sigma_Val s)
( at level 7, left associativity, only printing)  : subst_scope.

Notation "↑__Val" := up_Val (only printing)  : subst_scope.

Notation "↑__Val" := up_Val_Val (only printing)  : subst_scope.

Notation "s ⟨ xi_Val ⟩" := (ren_Tm xi_Val s)
( at level 7, left associativity, only printing)  : subst_scope.

Notation "s ⟨ xi_Val ⟩" := (ren_Val xi_Val s)
( at level 7, left associativity, only printing)  : subst_scope.

Notation "'var'" := var ( at level 1, only printing)  : subst_scope.

Notation "x '__Val'" := (@ids _ _ VarInstance_Val x)
( at level 5, format "x __Val", only printing)  : subst_scope.

Notation "x '__Val'" := (var x) ( at level 5, format "x __Val")  :
subst_scope.

#[global]
Instance subst_Tm_morphism  {m_Val : nat} {n_Val : nat}:
 (Proper (respectful (pointwise_relation _ eq) (respectful eq eq))
    (@subst_Tm m_Val n_Val)).
Proof.
exact (fun f_Val g_Val Eq_Val s t Eq_st =>
       eq_ind s (fun t' => subst_Tm f_Val s = subst_Tm g_Val t')
         (ext_Tm f_Val g_Val Eq_Val s) t Eq_st).
Qed.

#[global]
Instance subst_Tm_morphism2  {m_Val : nat} {n_Val : nat}:
 (Proper (respectful (pointwise_relation _ eq) (pointwise_relation _ eq))
    (@subst_Tm m_Val n_Val)).
Proof.
exact (fun f_Val g_Val Eq_Val s => ext_Tm f_Val g_Val Eq_Val s).
Qed.

#[global]
Instance subst_Val_morphism  {m_Val : nat} {n_Val : nat}:
 (Proper (respectful (pointwise_relation _ eq) (respectful eq eq))
    (@subst_Val m_Val n_Val)).
Proof.
exact (fun f_Val g_Val Eq_Val s t Eq_st =>
       eq_ind s (fun t' => subst_Val f_Val s = subst_Val g_Val t')
         (ext_Val f_Val g_Val Eq_Val s) t Eq_st).
Qed.

#[global]
Instance subst_Val_morphism2  {m_Val : nat} {n_Val : nat}:
 (Proper (respectful (pointwise_relation _ eq) (pointwise_relation _ eq))
    (@subst_Val m_Val n_Val)).
Proof.
exact (fun f_Val g_Val Eq_Val s => ext_Val f_Val g_Val Eq_Val s).
Qed.

#[global]
Instance ren_Tm_morphism  {m_Val : nat} {n_Val : nat}:
 (Proper (respectful (pointwise_relation _ eq) (respectful eq eq))
    (@ren_Tm m_Val n_Val)).
Proof.
exact (fun f_Val g_Val Eq_Val s t Eq_st =>
       eq_ind s (fun t' => ren_Tm f_Val s = ren_Tm g_Val t')
         (extRen_Tm f_Val g_Val Eq_Val s) t Eq_st).
Qed.

#[global]
Instance ren_Tm_morphism2  {m_Val : nat} {n_Val : nat}:
 (Proper (respectful (pointwise_relation _ eq) (pointwise_relation _ eq))
    (@ren_Tm m_Val n_Val)).
Proof.
exact (fun f_Val g_Val Eq_Val s => extRen_Tm f_Val g_Val Eq_Val s).
Qed.

#[global]
Instance ren_Val_morphism  {m_Val : nat} {n_Val : nat}:
 (Proper (respectful (pointwise_relation _ eq) (respectful eq eq))
    (@ren_Val m_Val n_Val)).
Proof.
exact (fun f_Val g_Val Eq_Val s t Eq_st =>
       eq_ind s (fun t' => ren_Val f_Val s = ren_Val g_Val t')
         (extRen_Val f_Val g_Val Eq_Val s) t Eq_st).
Qed.

#[global]
Instance ren_Val_morphism2  {m_Val : nat} {n_Val : nat}:
 (Proper (respectful (pointwise_relation _ eq) (pointwise_relation _ eq))
    (@ren_Val m_Val n_Val)).
Proof.
exact (fun f_Val g_Val Eq_Val s => extRen_Val f_Val g_Val Eq_Val s).
Qed.

Ltac auto_unfold := repeat
                     unfold VarInstance_Val, Var, ids, Ren_Val, Ren1, ren1,
                      Ren_Tm, Ren1, ren1, Up_Val_Val, Up_Val, up_Val,
                      Subst_Val, Subst1, subst1, Subst_Tm, Subst1, subst1.

Tactic Notation "auto_unfold" "in" "*" := repeat
                                           unfold VarInstance_Val, Var, ids,
                                            Ren_Val, Ren1, ren1, Ren_Tm,
                                            Ren1, ren1, Up_Val_Val, Up_Val,
                                            up_Val, Subst_Val, Subst1,
                                            subst1, Subst_Tm, Subst1, subst1
                                            in *.

Ltac asimpl' := repeat (first
                 [ progress setoid_rewrite substSubst_Tm_pointwise
                 | progress setoid_rewrite substSubst_Tm
                 | progress setoid_rewrite substSubst_Val_pointwise
                 | progress setoid_rewrite substSubst_Val
                 | progress setoid_rewrite substRen_Tm_pointwise
                 | progress setoid_rewrite substRen_Tm
                 | progress setoid_rewrite substRen_Val_pointwise
                 | progress setoid_rewrite substRen_Val
                 | progress setoid_rewrite renSubst_Tm_pointwise
                 | progress setoid_rewrite renSubst_Tm
                 | progress setoid_rewrite renSubst_Val_pointwise
                 | progress setoid_rewrite renSubst_Val
                 | progress setoid_rewrite renRen'_Tm_pointwise
                 | progress setoid_rewrite renRen_Tm
                 | progress setoid_rewrite renRen'_Val_pointwise
                 | progress setoid_rewrite renRen_Val
                 | progress setoid_rewrite varLRen'_Val_pointwise
                 | progress setoid_rewrite varLRen'_Val
                 | progress setoid_rewrite varL'_Val_pointwise
                 | progress setoid_rewrite varL'_Val
                 | progress setoid_rewrite rinstId'_Tm_pointwise
                 | progress setoid_rewrite rinstId'_Tm
                 | progress setoid_rewrite rinstId'_Val_pointwise
                 | progress setoid_rewrite rinstId'_Val
                 | progress setoid_rewrite instId'_Tm_pointwise
                 | progress setoid_rewrite instId'_Tm
                 | progress setoid_rewrite instId'_Val_pointwise
                 | progress setoid_rewrite instId'_Val
                 | progress
                    unfold up_list_Val_Val, up_Val_Val, upRen_list_Val_Val,
                     upRen_Val_Val, up_ren
                 | progress cbn[subst_Tm subst_Val ren_Tm ren_Val]
                 | progress fsimpl ]).

Ltac asimpl := check_no_evars;
                repeat
                 unfold VarInstance_Val, Var, ids, Ren_Val, Ren1, ren1,
                  Ren_Tm, Ren1, ren1, Up_Val_Val, Up_Val, up_Val, Subst_Val,
                  Subst1, subst1, Subst_Tm, Subst1, subst1 in *;
                asimpl'; minimize.

Tactic Notation "asimpl" "in" hyp(J) := revert J; asimpl; intros J.

Tactic Notation "auto_case" := auto_case ltac:(asimpl; cbn; eauto).

Ltac substify := auto_unfold; try setoid_rewrite rinstInst'_Tm_pointwise;
                  try setoid_rewrite rinstInst'_Tm;
                  try setoid_rewrite rinstInst'_Val_pointwise;
                  try setoid_rewrite rinstInst'_Val.

Ltac renamify := auto_unfold; try setoid_rewrite_left rinstInst'_Tm_pointwise;
                  try setoid_rewrite_left rinstInst'_Tm;
                  try setoid_rewrite_left rinstInst'_Val_pointwise;
                  try setoid_rewrite_left rinstInst'_Val.

End Core.

Module Extra.

Import
Core.

Arguments bind {n_Val}.

Arguments box {n_Val}.

Arguments unfold {n_Val}.

Arguments app {n_Val}.

Arguments case {n_Val}.

Arguments split {n_Val}.

Arguments prj {n_Val}.

Arguments ifz {n_Val}.

Arguments let_ {n_Val}.

Arguments ret {n_Val}.

Arguments var {n_Val}.

Arguments fold {n_Val}.

Arguments rec {n_Val}.

Arguments abs {n_Val}.

Arguments inj {n_Val}.

Arguments prod {n_Val}.

Arguments succ {n_Val}.

Arguments zero {n_Val}.

#[global] Hint Opaque subst_Tm: rewrite.

#[global] Hint Opaque subst_Val: rewrite.

#[global] Hint Opaque ren_Tm: rewrite.

#[global] Hint Opaque ren_Val: rewrite.

End Extra.

Module interface.

Export Core.

Export Extra.

End interface.

Export interface.

