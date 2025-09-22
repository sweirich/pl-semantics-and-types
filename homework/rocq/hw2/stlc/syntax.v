Require Import core fintype.

Require Import Setoid Morphisms Relation_Definitions.


Module Core.

Inductive Tm (n_Tm : nat) : Type :=
  | var : fin n_Tm -> Tm n_Tm
  | abs : Tm (S n_Tm) -> Tm n_Tm
  | app : Tm n_Tm -> Tm n_Tm -> Tm n_Tm
  | lit : nat -> Tm n_Tm
  | succ : Tm n_Tm -> Tm n_Tm
  | nrec : Tm n_Tm -> Tm n_Tm -> Tm (S n_Tm) -> Tm n_Tm
  | let_ : Tm n_Tm -> Tm (S n_Tm) -> Tm n_Tm.

Lemma congr_abs {m_Tm : nat} {s0 : Tm (S m_Tm)} {t0 : Tm (S m_Tm)}
  (H0 : s0 = t0) : abs m_Tm s0 = abs m_Tm t0.
Proof.
exact (eq_trans eq_refl (ap (fun x => abs m_Tm x) H0)).
Qed.

Lemma congr_app {m_Tm : nat} {s0 : Tm m_Tm} {s1 : Tm m_Tm} {t0 : Tm m_Tm}
  {t1 : Tm m_Tm} (H0 : s0 = t0) (H1 : s1 = t1) :
  app m_Tm s0 s1 = app m_Tm t0 t1.
Proof.
exact (eq_trans (eq_trans eq_refl (ap (fun x => app m_Tm x s1) H0))
         (ap (fun x => app m_Tm t0 x) H1)).
Qed.

Lemma congr_lit {m_Tm : nat} {s0 : nat} {t0 : nat} (H0 : s0 = t0) :
  lit m_Tm s0 = lit m_Tm t0.
Proof.
exact (eq_trans eq_refl (ap (fun x => lit m_Tm x) H0)).
Qed.

Lemma congr_succ {m_Tm : nat} {s0 : Tm m_Tm} {t0 : Tm m_Tm} (H0 : s0 = t0) :
  succ m_Tm s0 = succ m_Tm t0.
Proof.
exact (eq_trans eq_refl (ap (fun x => succ m_Tm x) H0)).
Qed.

Lemma congr_nrec {m_Tm : nat} {s0 : Tm m_Tm} {s1 : Tm m_Tm}
  {s2 : Tm (S m_Tm)} {t0 : Tm m_Tm} {t1 : Tm m_Tm} {t2 : Tm (S m_Tm)}
  (H0 : s0 = t0) (H1 : s1 = t1) (H2 : s2 = t2) :
  nrec m_Tm s0 s1 s2 = nrec m_Tm t0 t1 t2.
Proof.
exact (eq_trans
         (eq_trans (eq_trans eq_refl (ap (fun x => nrec m_Tm x s1 s2) H0))
            (ap (fun x => nrec m_Tm t0 x s2) H1))
         (ap (fun x => nrec m_Tm t0 t1 x) H2)).
Qed.

Lemma congr_let_ {m_Tm : nat} {s0 : Tm m_Tm} {s1 : Tm (S m_Tm)}
  {t0 : Tm m_Tm} {t1 : Tm (S m_Tm)} (H0 : s0 = t0) (H1 : s1 = t1) :
  let_ m_Tm s0 s1 = let_ m_Tm t0 t1.
Proof.
exact (eq_trans (eq_trans eq_refl (ap (fun x => let_ m_Tm x s1) H0))
         (ap (fun x => let_ m_Tm t0 x) H1)).
Qed.

Lemma upRen_Tm_Tm {m : nat} {n : nat} (xi : fin m -> fin n) :
  fin (S m) -> fin (S n).
Proof.
exact (up_ren xi).
Defined.

Lemma upRen_list_Tm_Tm (p : nat) {m : nat} {n : nat} (xi : fin m -> fin n) :
  fin (plus p m) -> fin (plus p n).
Proof.
exact (upRen_p p xi).
Defined.

Fixpoint ren_Tm {m_Tm : nat} {n_Tm : nat} (xi_Tm : fin m_Tm -> fin n_Tm)
(s : Tm m_Tm) {struct s} : Tm n_Tm :=
  match s with
  | var _ s0 => var n_Tm (xi_Tm s0)
  | abs _ s0 => abs n_Tm (ren_Tm (upRen_Tm_Tm xi_Tm) s0)
  | app _ s0 s1 => app n_Tm (ren_Tm xi_Tm s0) (ren_Tm xi_Tm s1)
  | lit _ s0 => lit n_Tm s0
  | succ _ s0 => succ n_Tm (ren_Tm xi_Tm s0)
  | nrec _ s0 s1 s2 =>
      nrec n_Tm (ren_Tm xi_Tm s0) (ren_Tm xi_Tm s1)
        (ren_Tm (upRen_Tm_Tm xi_Tm) s2)
  | let_ _ s0 s1 =>
      let_ n_Tm (ren_Tm xi_Tm s0) (ren_Tm (upRen_Tm_Tm xi_Tm) s1)
  end.

Lemma up_Tm_Tm {m : nat} {n_Tm : nat} (sigma : fin m -> Tm n_Tm) :
  fin (S m) -> Tm (S n_Tm).
Proof.
exact (scons (var (S n_Tm) var_zero) (funcomp (ren_Tm shift) sigma)).
Defined.

Lemma up_list_Tm_Tm (p : nat) {m : nat} {n_Tm : nat}
  (sigma : fin m -> Tm n_Tm) : fin (plus p m) -> Tm (plus p n_Tm).
Proof.
exact (scons_p p (funcomp (var (plus p n_Tm)) (zero_p p))
         (funcomp (ren_Tm (shift_p p)) sigma)).
Defined.

Fixpoint subst_Tm {m_Tm : nat} {n_Tm : nat} (sigma_Tm : fin m_Tm -> Tm n_Tm)
(s : Tm m_Tm) {struct s} : Tm n_Tm :=
  match s with
  | var _ s0 => sigma_Tm s0
  | abs _ s0 => abs n_Tm (subst_Tm (up_Tm_Tm sigma_Tm) s0)
  | app _ s0 s1 => app n_Tm (subst_Tm sigma_Tm s0) (subst_Tm sigma_Tm s1)
  | lit _ s0 => lit n_Tm s0
  | succ _ s0 => succ n_Tm (subst_Tm sigma_Tm s0)
  | nrec _ s0 s1 s2 =>
      nrec n_Tm (subst_Tm sigma_Tm s0) (subst_Tm sigma_Tm s1)
        (subst_Tm (up_Tm_Tm sigma_Tm) s2)
  | let_ _ s0 s1 =>
      let_ n_Tm (subst_Tm sigma_Tm s0) (subst_Tm (up_Tm_Tm sigma_Tm) s1)
  end.

Lemma upId_Tm_Tm {m_Tm : nat} (sigma : fin m_Tm -> Tm m_Tm)
  (Eq : forall x, sigma x = var m_Tm x) :
  forall x, up_Tm_Tm sigma x = var (S m_Tm) x.
Proof.
exact (fun n =>
       match n with
       | Some fin_n => ap (ren_Tm shift) (Eq fin_n)
       | None => eq_refl
       end).
Qed.

Lemma upId_list_Tm_Tm {p : nat} {m_Tm : nat} (sigma : fin m_Tm -> Tm m_Tm)
  (Eq : forall x, sigma x = var m_Tm x) :
  forall x, up_list_Tm_Tm p sigma x = var (plus p m_Tm) x.
Proof.
exact (fun n =>
       scons_p_eta (var (plus p m_Tm))
         (fun n => ap (ren_Tm (shift_p p)) (Eq n)) (fun n => eq_refl)).
Qed.

Fixpoint idSubst_Tm {m_Tm : nat} (sigma_Tm : fin m_Tm -> Tm m_Tm)
(Eq_Tm : forall x, sigma_Tm x = var m_Tm x) (s : Tm m_Tm) {struct s} :
subst_Tm sigma_Tm s = s :=
  match s with
  | var _ s0 => Eq_Tm s0
  | abs _ s0 =>
      congr_abs (idSubst_Tm (up_Tm_Tm sigma_Tm) (upId_Tm_Tm _ Eq_Tm) s0)
  | app _ s0 s1 =>
      congr_app (idSubst_Tm sigma_Tm Eq_Tm s0) (idSubst_Tm sigma_Tm Eq_Tm s1)
  | lit _ s0 => congr_lit (eq_refl s0)
  | succ _ s0 => congr_succ (idSubst_Tm sigma_Tm Eq_Tm s0)
  | nrec _ s0 s1 s2 =>
      congr_nrec (idSubst_Tm sigma_Tm Eq_Tm s0)
        (idSubst_Tm sigma_Tm Eq_Tm s1)
        (idSubst_Tm (up_Tm_Tm sigma_Tm) (upId_Tm_Tm _ Eq_Tm) s2)
  | let_ _ s0 s1 =>
      congr_let_ (idSubst_Tm sigma_Tm Eq_Tm s0)
        (idSubst_Tm (up_Tm_Tm sigma_Tm) (upId_Tm_Tm _ Eq_Tm) s1)
  end.

Lemma upExtRen_Tm_Tm {m : nat} {n : nat} (xi : fin m -> fin n)
  (zeta : fin m -> fin n) (Eq : forall x, xi x = zeta x) :
  forall x, upRen_Tm_Tm xi x = upRen_Tm_Tm zeta x.
Proof.
exact (fun n =>
       match n with
       | Some fin_n => ap shift (Eq fin_n)
       | None => eq_refl
       end).
Qed.

Lemma upExtRen_list_Tm_Tm {p : nat} {m : nat} {n : nat} (xi : fin m -> fin n)
  (zeta : fin m -> fin n) (Eq : forall x, xi x = zeta x) :
  forall x, upRen_list_Tm_Tm p xi x = upRen_list_Tm_Tm p zeta x.
Proof.
exact (fun n =>
       scons_p_congr (fun n => eq_refl) (fun n => ap (shift_p p) (Eq n))).
Qed.

Fixpoint extRen_Tm {m_Tm : nat} {n_Tm : nat} (xi_Tm : fin m_Tm -> fin n_Tm)
(zeta_Tm : fin m_Tm -> fin n_Tm) (Eq_Tm : forall x, xi_Tm x = zeta_Tm x)
(s : Tm m_Tm) {struct s} : ren_Tm xi_Tm s = ren_Tm zeta_Tm s :=
  match s with
  | var _ s0 => ap (var n_Tm) (Eq_Tm s0)
  | abs _ s0 =>
      congr_abs
        (extRen_Tm (upRen_Tm_Tm xi_Tm) (upRen_Tm_Tm zeta_Tm)
           (upExtRen_Tm_Tm _ _ Eq_Tm) s0)
  | app _ s0 s1 =>
      congr_app (extRen_Tm xi_Tm zeta_Tm Eq_Tm s0)
        (extRen_Tm xi_Tm zeta_Tm Eq_Tm s1)
  | lit _ s0 => congr_lit (eq_refl s0)
  | succ _ s0 => congr_succ (extRen_Tm xi_Tm zeta_Tm Eq_Tm s0)
  | nrec _ s0 s1 s2 =>
      congr_nrec (extRen_Tm xi_Tm zeta_Tm Eq_Tm s0)
        (extRen_Tm xi_Tm zeta_Tm Eq_Tm s1)
        (extRen_Tm (upRen_Tm_Tm xi_Tm) (upRen_Tm_Tm zeta_Tm)
           (upExtRen_Tm_Tm _ _ Eq_Tm) s2)
  | let_ _ s0 s1 =>
      congr_let_ (extRen_Tm xi_Tm zeta_Tm Eq_Tm s0)
        (extRen_Tm (upRen_Tm_Tm xi_Tm) (upRen_Tm_Tm zeta_Tm)
           (upExtRen_Tm_Tm _ _ Eq_Tm) s1)
  end.

Lemma upExt_Tm_Tm {m : nat} {n_Tm : nat} (sigma : fin m -> Tm n_Tm)
  (tau : fin m -> Tm n_Tm) (Eq : forall x, sigma x = tau x) :
  forall x, up_Tm_Tm sigma x = up_Tm_Tm tau x.
Proof.
exact (fun n =>
       match n with
       | Some fin_n => ap (ren_Tm shift) (Eq fin_n)
       | None => eq_refl
       end).
Qed.

Lemma upExt_list_Tm_Tm {p : nat} {m : nat} {n_Tm : nat}
  (sigma : fin m -> Tm n_Tm) (tau : fin m -> Tm n_Tm)
  (Eq : forall x, sigma x = tau x) :
  forall x, up_list_Tm_Tm p sigma x = up_list_Tm_Tm p tau x.
Proof.
exact (fun n =>
       scons_p_congr (fun n => eq_refl)
         (fun n => ap (ren_Tm (shift_p p)) (Eq n))).
Qed.

Fixpoint ext_Tm {m_Tm : nat} {n_Tm : nat} (sigma_Tm : fin m_Tm -> Tm n_Tm)
(tau_Tm : fin m_Tm -> Tm n_Tm) (Eq_Tm : forall x, sigma_Tm x = tau_Tm x)
(s : Tm m_Tm) {struct s} : subst_Tm sigma_Tm s = subst_Tm tau_Tm s :=
  match s with
  | var _ s0 => Eq_Tm s0
  | abs _ s0 =>
      congr_abs
        (ext_Tm (up_Tm_Tm sigma_Tm) (up_Tm_Tm tau_Tm) (upExt_Tm_Tm _ _ Eq_Tm)
           s0)
  | app _ s0 s1 =>
      congr_app (ext_Tm sigma_Tm tau_Tm Eq_Tm s0)
        (ext_Tm sigma_Tm tau_Tm Eq_Tm s1)
  | lit _ s0 => congr_lit (eq_refl s0)
  | succ _ s0 => congr_succ (ext_Tm sigma_Tm tau_Tm Eq_Tm s0)
  | nrec _ s0 s1 s2 =>
      congr_nrec (ext_Tm sigma_Tm tau_Tm Eq_Tm s0)
        (ext_Tm sigma_Tm tau_Tm Eq_Tm s1)
        (ext_Tm (up_Tm_Tm sigma_Tm) (up_Tm_Tm tau_Tm) (upExt_Tm_Tm _ _ Eq_Tm)
           s2)
  | let_ _ s0 s1 =>
      congr_let_ (ext_Tm sigma_Tm tau_Tm Eq_Tm s0)
        (ext_Tm (up_Tm_Tm sigma_Tm) (up_Tm_Tm tau_Tm) (upExt_Tm_Tm _ _ Eq_Tm)
           s1)
  end.

Lemma up_ren_ren_Tm_Tm {k : nat} {l : nat} {m : nat} (xi : fin k -> fin l)
  (zeta : fin l -> fin m) (rho : fin k -> fin m)
  (Eq : forall x, funcomp zeta xi x = rho x) :
  forall x, funcomp (upRen_Tm_Tm zeta) (upRen_Tm_Tm xi) x = upRen_Tm_Tm rho x.
Proof.
exact (up_ren_ren xi zeta rho Eq).
Qed.

Lemma up_ren_ren_list_Tm_Tm {p : nat} {k : nat} {l : nat} {m : nat}
  (xi : fin k -> fin l) (zeta : fin l -> fin m) (rho : fin k -> fin m)
  (Eq : forall x, funcomp zeta xi x = rho x) :
  forall x,
  funcomp (upRen_list_Tm_Tm p zeta) (upRen_list_Tm_Tm p xi) x =
  upRen_list_Tm_Tm p rho x.
Proof.
exact (up_ren_ren_p Eq).
Qed.

Fixpoint compRenRen_Tm {k_Tm : nat} {l_Tm : nat} {m_Tm : nat}
(xi_Tm : fin m_Tm -> fin k_Tm) (zeta_Tm : fin k_Tm -> fin l_Tm)
(rho_Tm : fin m_Tm -> fin l_Tm)
(Eq_Tm : forall x, funcomp zeta_Tm xi_Tm x = rho_Tm x) (s : Tm m_Tm) {struct
 s} :
ren_Tm zeta_Tm (ren_Tm xi_Tm s) = ren_Tm rho_Tm s :=
  match s with
  | var _ s0 => ap (var l_Tm) (Eq_Tm s0)
  | abs _ s0 =>
      congr_abs
        (compRenRen_Tm (upRen_Tm_Tm xi_Tm) (upRen_Tm_Tm zeta_Tm)
           (upRen_Tm_Tm rho_Tm) (up_ren_ren _ _ _ Eq_Tm) s0)
  | app _ s0 s1 =>
      congr_app (compRenRen_Tm xi_Tm zeta_Tm rho_Tm Eq_Tm s0)
        (compRenRen_Tm xi_Tm zeta_Tm rho_Tm Eq_Tm s1)
  | lit _ s0 => congr_lit (eq_refl s0)
  | succ _ s0 => congr_succ (compRenRen_Tm xi_Tm zeta_Tm rho_Tm Eq_Tm s0)
  | nrec _ s0 s1 s2 =>
      congr_nrec (compRenRen_Tm xi_Tm zeta_Tm rho_Tm Eq_Tm s0)
        (compRenRen_Tm xi_Tm zeta_Tm rho_Tm Eq_Tm s1)
        (compRenRen_Tm (upRen_Tm_Tm xi_Tm) (upRen_Tm_Tm zeta_Tm)
           (upRen_Tm_Tm rho_Tm) (up_ren_ren _ _ _ Eq_Tm) s2)
  | let_ _ s0 s1 =>
      congr_let_ (compRenRen_Tm xi_Tm zeta_Tm rho_Tm Eq_Tm s0)
        (compRenRen_Tm (upRen_Tm_Tm xi_Tm) (upRen_Tm_Tm zeta_Tm)
           (upRen_Tm_Tm rho_Tm) (up_ren_ren _ _ _ Eq_Tm) s1)
  end.

Lemma up_ren_subst_Tm_Tm {k : nat} {l : nat} {m_Tm : nat}
  (xi : fin k -> fin l) (tau : fin l -> Tm m_Tm) (theta : fin k -> Tm m_Tm)
  (Eq : forall x, funcomp tau xi x = theta x) :
  forall x, funcomp (up_Tm_Tm tau) (upRen_Tm_Tm xi) x = up_Tm_Tm theta x.
Proof.
exact (fun n =>
       match n with
       | Some fin_n => ap (ren_Tm shift) (Eq fin_n)
       | None => eq_refl
       end).
Qed.

Lemma up_ren_subst_list_Tm_Tm {p : nat} {k : nat} {l : nat} {m_Tm : nat}
  (xi : fin k -> fin l) (tau : fin l -> Tm m_Tm) (theta : fin k -> Tm m_Tm)
  (Eq : forall x, funcomp tau xi x = theta x) :
  forall x,
  funcomp (up_list_Tm_Tm p tau) (upRen_list_Tm_Tm p xi) x =
  up_list_Tm_Tm p theta x.
Proof.
exact (fun n =>
       eq_trans (scons_p_comp' _ _ _ n)
         (scons_p_congr (fun z => scons_p_head' _ _ z)
            (fun z =>
             eq_trans (scons_p_tail' _ _ (xi z))
               (ap (ren_Tm (shift_p p)) (Eq z))))).
Qed.

Fixpoint compRenSubst_Tm {k_Tm : nat} {l_Tm : nat} {m_Tm : nat}
(xi_Tm : fin m_Tm -> fin k_Tm) (tau_Tm : fin k_Tm -> Tm l_Tm)
(theta_Tm : fin m_Tm -> Tm l_Tm)
(Eq_Tm : forall x, funcomp tau_Tm xi_Tm x = theta_Tm x) (s : Tm m_Tm) {struct
 s} :
subst_Tm tau_Tm (ren_Tm xi_Tm s) = subst_Tm theta_Tm s :=
  match s with
  | var _ s0 => Eq_Tm s0
  | abs _ s0 =>
      congr_abs
        (compRenSubst_Tm (upRen_Tm_Tm xi_Tm) (up_Tm_Tm tau_Tm)
           (up_Tm_Tm theta_Tm) (up_ren_subst_Tm_Tm _ _ _ Eq_Tm) s0)
  | app _ s0 s1 =>
      congr_app (compRenSubst_Tm xi_Tm tau_Tm theta_Tm Eq_Tm s0)
        (compRenSubst_Tm xi_Tm tau_Tm theta_Tm Eq_Tm s1)
  | lit _ s0 => congr_lit (eq_refl s0)
  | succ _ s0 => congr_succ (compRenSubst_Tm xi_Tm tau_Tm theta_Tm Eq_Tm s0)
  | nrec _ s0 s1 s2 =>
      congr_nrec (compRenSubst_Tm xi_Tm tau_Tm theta_Tm Eq_Tm s0)
        (compRenSubst_Tm xi_Tm tau_Tm theta_Tm Eq_Tm s1)
        (compRenSubst_Tm (upRen_Tm_Tm xi_Tm) (up_Tm_Tm tau_Tm)
           (up_Tm_Tm theta_Tm) (up_ren_subst_Tm_Tm _ _ _ Eq_Tm) s2)
  | let_ _ s0 s1 =>
      congr_let_ (compRenSubst_Tm xi_Tm tau_Tm theta_Tm Eq_Tm s0)
        (compRenSubst_Tm (upRen_Tm_Tm xi_Tm) (up_Tm_Tm tau_Tm)
           (up_Tm_Tm theta_Tm) (up_ren_subst_Tm_Tm _ _ _ Eq_Tm) s1)
  end.

Lemma up_subst_ren_Tm_Tm {k : nat} {l_Tm : nat} {m_Tm : nat}
  (sigma : fin k -> Tm l_Tm) (zeta_Tm : fin l_Tm -> fin m_Tm)
  (theta : fin k -> Tm m_Tm)
  (Eq : forall x, funcomp (ren_Tm zeta_Tm) sigma x = theta x) :
  forall x,
  funcomp (ren_Tm (upRen_Tm_Tm zeta_Tm)) (up_Tm_Tm sigma) x =
  up_Tm_Tm theta x.
Proof.
exact (fun n =>
       match n with
       | Some fin_n =>
           eq_trans
             (compRenRen_Tm shift (upRen_Tm_Tm zeta_Tm)
                (funcomp shift zeta_Tm) (fun x => eq_refl) (sigma fin_n))
             (eq_trans
                (eq_sym
                   (compRenRen_Tm zeta_Tm shift (funcomp shift zeta_Tm)
                      (fun x => eq_refl) (sigma fin_n)))
                (ap (ren_Tm shift) (Eq fin_n)))
       | None => eq_refl
       end).
Qed.

Lemma up_subst_ren_list_Tm_Tm {p : nat} {k : nat} {l_Tm : nat} {m_Tm : nat}
  (sigma : fin k -> Tm l_Tm) (zeta_Tm : fin l_Tm -> fin m_Tm)
  (theta : fin k -> Tm m_Tm)
  (Eq : forall x, funcomp (ren_Tm zeta_Tm) sigma x = theta x) :
  forall x,
  funcomp (ren_Tm (upRen_list_Tm_Tm p zeta_Tm)) (up_list_Tm_Tm p sigma) x =
  up_list_Tm_Tm p theta x.
Proof.
exact (fun n =>
       eq_trans (scons_p_comp' _ _ _ n)
         (scons_p_congr
            (fun x => ap (var (plus p m_Tm)) (scons_p_head' _ _ x))
            (fun n =>
             eq_trans
               (compRenRen_Tm (shift_p p) (upRen_list_Tm_Tm p zeta_Tm)
                  (funcomp (shift_p p) zeta_Tm)
                  (fun x => scons_p_tail' _ _ x) (sigma n))
               (eq_trans
                  (eq_sym
                     (compRenRen_Tm zeta_Tm (shift_p p)
                        (funcomp (shift_p p) zeta_Tm) (fun x => eq_refl)
                        (sigma n)))
                  (ap (ren_Tm (shift_p p)) (Eq n)))))).
Qed.

Fixpoint compSubstRen_Tm {k_Tm : nat} {l_Tm : nat} {m_Tm : nat}
(sigma_Tm : fin m_Tm -> Tm k_Tm) (zeta_Tm : fin k_Tm -> fin l_Tm)
(theta_Tm : fin m_Tm -> Tm l_Tm)
(Eq_Tm : forall x, funcomp (ren_Tm zeta_Tm) sigma_Tm x = theta_Tm x)
(s : Tm m_Tm) {struct s} :
ren_Tm zeta_Tm (subst_Tm sigma_Tm s) = subst_Tm theta_Tm s :=
  match s with
  | var _ s0 => Eq_Tm s0
  | abs _ s0 =>
      congr_abs
        (compSubstRen_Tm (up_Tm_Tm sigma_Tm) (upRen_Tm_Tm zeta_Tm)
           (up_Tm_Tm theta_Tm) (up_subst_ren_Tm_Tm _ _ _ Eq_Tm) s0)
  | app _ s0 s1 =>
      congr_app (compSubstRen_Tm sigma_Tm zeta_Tm theta_Tm Eq_Tm s0)
        (compSubstRen_Tm sigma_Tm zeta_Tm theta_Tm Eq_Tm s1)
  | lit _ s0 => congr_lit (eq_refl s0)
  | succ _ s0 =>
      congr_succ (compSubstRen_Tm sigma_Tm zeta_Tm theta_Tm Eq_Tm s0)
  | nrec _ s0 s1 s2 =>
      congr_nrec (compSubstRen_Tm sigma_Tm zeta_Tm theta_Tm Eq_Tm s0)
        (compSubstRen_Tm sigma_Tm zeta_Tm theta_Tm Eq_Tm s1)
        (compSubstRen_Tm (up_Tm_Tm sigma_Tm) (upRen_Tm_Tm zeta_Tm)
           (up_Tm_Tm theta_Tm) (up_subst_ren_Tm_Tm _ _ _ Eq_Tm) s2)
  | let_ _ s0 s1 =>
      congr_let_ (compSubstRen_Tm sigma_Tm zeta_Tm theta_Tm Eq_Tm s0)
        (compSubstRen_Tm (up_Tm_Tm sigma_Tm) (upRen_Tm_Tm zeta_Tm)
           (up_Tm_Tm theta_Tm) (up_subst_ren_Tm_Tm _ _ _ Eq_Tm) s1)
  end.

Lemma up_subst_subst_Tm_Tm {k : nat} {l_Tm : nat} {m_Tm : nat}
  (sigma : fin k -> Tm l_Tm) (tau_Tm : fin l_Tm -> Tm m_Tm)
  (theta : fin k -> Tm m_Tm)
  (Eq : forall x, funcomp (subst_Tm tau_Tm) sigma x = theta x) :
  forall x,
  funcomp (subst_Tm (up_Tm_Tm tau_Tm)) (up_Tm_Tm sigma) x = up_Tm_Tm theta x.
Proof.
exact (fun n =>
       match n with
       | Some fin_n =>
           eq_trans
             (compRenSubst_Tm shift (up_Tm_Tm tau_Tm)
                (funcomp (up_Tm_Tm tau_Tm) shift) (fun x => eq_refl)
                (sigma fin_n))
             (eq_trans
                (eq_sym
                   (compSubstRen_Tm tau_Tm shift
                      (funcomp (ren_Tm shift) tau_Tm) (fun x => eq_refl)
                      (sigma fin_n)))
                (ap (ren_Tm shift) (Eq fin_n)))
       | None => eq_refl
       end).
Qed.

Lemma up_subst_subst_list_Tm_Tm {p : nat} {k : nat} {l_Tm : nat} {m_Tm : nat}
  (sigma : fin k -> Tm l_Tm) (tau_Tm : fin l_Tm -> Tm m_Tm)
  (theta : fin k -> Tm m_Tm)
  (Eq : forall x, funcomp (subst_Tm tau_Tm) sigma x = theta x) :
  forall x,
  funcomp (subst_Tm (up_list_Tm_Tm p tau_Tm)) (up_list_Tm_Tm p sigma) x =
  up_list_Tm_Tm p theta x.
Proof.
exact (fun n =>
       eq_trans
         (scons_p_comp' (funcomp (var (plus p l_Tm)) (zero_p p)) _ _ n)
         (scons_p_congr
            (fun x => scons_p_head' _ (fun z => ren_Tm (shift_p p) _) x)
            (fun n =>
             eq_trans
               (compRenSubst_Tm (shift_p p) (up_list_Tm_Tm p tau_Tm)
                  (funcomp (up_list_Tm_Tm p tau_Tm) (shift_p p))
                  (fun x => eq_refl) (sigma n))
               (eq_trans
                  (eq_sym
                     (compSubstRen_Tm tau_Tm (shift_p p) _
                        (fun x => eq_sym (scons_p_tail' _ _ x)) (sigma n)))
                  (ap (ren_Tm (shift_p p)) (Eq n)))))).
Qed.

Fixpoint compSubstSubst_Tm {k_Tm : nat} {l_Tm : nat} {m_Tm : nat}
(sigma_Tm : fin m_Tm -> Tm k_Tm) (tau_Tm : fin k_Tm -> Tm l_Tm)
(theta_Tm : fin m_Tm -> Tm l_Tm)
(Eq_Tm : forall x, funcomp (subst_Tm tau_Tm) sigma_Tm x = theta_Tm x)
(s : Tm m_Tm) {struct s} :
subst_Tm tau_Tm (subst_Tm sigma_Tm s) = subst_Tm theta_Tm s :=
  match s with
  | var _ s0 => Eq_Tm s0
  | abs _ s0 =>
      congr_abs
        (compSubstSubst_Tm (up_Tm_Tm sigma_Tm) (up_Tm_Tm tau_Tm)
           (up_Tm_Tm theta_Tm) (up_subst_subst_Tm_Tm _ _ _ Eq_Tm) s0)
  | app _ s0 s1 =>
      congr_app (compSubstSubst_Tm sigma_Tm tau_Tm theta_Tm Eq_Tm s0)
        (compSubstSubst_Tm sigma_Tm tau_Tm theta_Tm Eq_Tm s1)
  | lit _ s0 => congr_lit (eq_refl s0)
  | succ _ s0 =>
      congr_succ (compSubstSubst_Tm sigma_Tm tau_Tm theta_Tm Eq_Tm s0)
  | nrec _ s0 s1 s2 =>
      congr_nrec (compSubstSubst_Tm sigma_Tm tau_Tm theta_Tm Eq_Tm s0)
        (compSubstSubst_Tm sigma_Tm tau_Tm theta_Tm Eq_Tm s1)
        (compSubstSubst_Tm (up_Tm_Tm sigma_Tm) (up_Tm_Tm tau_Tm)
           (up_Tm_Tm theta_Tm) (up_subst_subst_Tm_Tm _ _ _ Eq_Tm) s2)
  | let_ _ s0 s1 =>
      congr_let_ (compSubstSubst_Tm sigma_Tm tau_Tm theta_Tm Eq_Tm s0)
        (compSubstSubst_Tm (up_Tm_Tm sigma_Tm) (up_Tm_Tm tau_Tm)
           (up_Tm_Tm theta_Tm) (up_subst_subst_Tm_Tm _ _ _ Eq_Tm) s1)
  end.

Lemma renRen_Tm {k_Tm : nat} {l_Tm : nat} {m_Tm : nat}
  (xi_Tm : fin m_Tm -> fin k_Tm) (zeta_Tm : fin k_Tm -> fin l_Tm)
  (s : Tm m_Tm) :
  ren_Tm zeta_Tm (ren_Tm xi_Tm s) = ren_Tm (funcomp zeta_Tm xi_Tm) s.
Proof.
exact (compRenRen_Tm xi_Tm zeta_Tm _ (fun n => eq_refl) s).
Qed.

Lemma renRen'_Tm_pointwise {k_Tm : nat} {l_Tm : nat} {m_Tm : nat}
  (xi_Tm : fin m_Tm -> fin k_Tm) (zeta_Tm : fin k_Tm -> fin l_Tm) :
  pointwise_relation _ eq (funcomp (ren_Tm zeta_Tm) (ren_Tm xi_Tm))
    (ren_Tm (funcomp zeta_Tm xi_Tm)).
Proof.
exact (fun s => compRenRen_Tm xi_Tm zeta_Tm _ (fun n => eq_refl) s).
Qed.

Lemma renSubst_Tm {k_Tm : nat} {l_Tm : nat} {m_Tm : nat}
  (xi_Tm : fin m_Tm -> fin k_Tm) (tau_Tm : fin k_Tm -> Tm l_Tm) (s : Tm m_Tm)
  : subst_Tm tau_Tm (ren_Tm xi_Tm s) = subst_Tm (funcomp tau_Tm xi_Tm) s.
Proof.
exact (compRenSubst_Tm xi_Tm tau_Tm _ (fun n => eq_refl) s).
Qed.

Lemma renSubst_Tm_pointwise {k_Tm : nat} {l_Tm : nat} {m_Tm : nat}
  (xi_Tm : fin m_Tm -> fin k_Tm) (tau_Tm : fin k_Tm -> Tm l_Tm) :
  pointwise_relation _ eq (funcomp (subst_Tm tau_Tm) (ren_Tm xi_Tm))
    (subst_Tm (funcomp tau_Tm xi_Tm)).
Proof.
exact (fun s => compRenSubst_Tm xi_Tm tau_Tm _ (fun n => eq_refl) s).
Qed.

Lemma substRen_Tm {k_Tm : nat} {l_Tm : nat} {m_Tm : nat}
  (sigma_Tm : fin m_Tm -> Tm k_Tm) (zeta_Tm : fin k_Tm -> fin l_Tm)
  (s : Tm m_Tm) :
  ren_Tm zeta_Tm (subst_Tm sigma_Tm s) =
  subst_Tm (funcomp (ren_Tm zeta_Tm) sigma_Tm) s.
Proof.
exact (compSubstRen_Tm sigma_Tm zeta_Tm _ (fun n => eq_refl) s).
Qed.

Lemma substRen_Tm_pointwise {k_Tm : nat} {l_Tm : nat} {m_Tm : nat}
  (sigma_Tm : fin m_Tm -> Tm k_Tm) (zeta_Tm : fin k_Tm -> fin l_Tm) :
  pointwise_relation _ eq (funcomp (ren_Tm zeta_Tm) (subst_Tm sigma_Tm))
    (subst_Tm (funcomp (ren_Tm zeta_Tm) sigma_Tm)).
Proof.
exact (fun s => compSubstRen_Tm sigma_Tm zeta_Tm _ (fun n => eq_refl) s).
Qed.

Lemma substSubst_Tm {k_Tm : nat} {l_Tm : nat} {m_Tm : nat}
  (sigma_Tm : fin m_Tm -> Tm k_Tm) (tau_Tm : fin k_Tm -> Tm l_Tm)
  (s : Tm m_Tm) :
  subst_Tm tau_Tm (subst_Tm sigma_Tm s) =
  subst_Tm (funcomp (subst_Tm tau_Tm) sigma_Tm) s.
Proof.
exact (compSubstSubst_Tm sigma_Tm tau_Tm _ (fun n => eq_refl) s).
Qed.

Lemma substSubst_Tm_pointwise {k_Tm : nat} {l_Tm : nat} {m_Tm : nat}
  (sigma_Tm : fin m_Tm -> Tm k_Tm) (tau_Tm : fin k_Tm -> Tm l_Tm) :
  pointwise_relation _ eq (funcomp (subst_Tm tau_Tm) (subst_Tm sigma_Tm))
    (subst_Tm (funcomp (subst_Tm tau_Tm) sigma_Tm)).
Proof.
exact (fun s => compSubstSubst_Tm sigma_Tm tau_Tm _ (fun n => eq_refl) s).
Qed.

Lemma rinstInst_up_Tm_Tm {m : nat} {n_Tm : nat} (xi : fin m -> fin n_Tm)
  (sigma : fin m -> Tm n_Tm)
  (Eq : forall x, funcomp (var n_Tm) xi x = sigma x) :
  forall x, funcomp (var (S n_Tm)) (upRen_Tm_Tm xi) x = up_Tm_Tm sigma x.
Proof.
exact (fun n =>
       match n with
       | Some fin_n => ap (ren_Tm shift) (Eq fin_n)
       | None => eq_refl
       end).
Qed.

Lemma rinstInst_up_list_Tm_Tm {p : nat} {m : nat} {n_Tm : nat}
  (xi : fin m -> fin n_Tm) (sigma : fin m -> Tm n_Tm)
  (Eq : forall x, funcomp (var n_Tm) xi x = sigma x) :
  forall x,
  funcomp (var (plus p n_Tm)) (upRen_list_Tm_Tm p xi) x =
  up_list_Tm_Tm p sigma x.
Proof.
exact (fun n =>
       eq_trans (scons_p_comp' _ _ (var (plus p n_Tm)) n)
         (scons_p_congr (fun z => eq_refl)
            (fun n => ap (ren_Tm (shift_p p)) (Eq n)))).
Qed.

Fixpoint rinst_inst_Tm {m_Tm : nat} {n_Tm : nat}
(xi_Tm : fin m_Tm -> fin n_Tm) (sigma_Tm : fin m_Tm -> Tm n_Tm)
(Eq_Tm : forall x, funcomp (var n_Tm) xi_Tm x = sigma_Tm x) (s : Tm m_Tm)
{struct s} : ren_Tm xi_Tm s = subst_Tm sigma_Tm s :=
  match s with
  | var _ s0 => Eq_Tm s0
  | abs _ s0 =>
      congr_abs
        (rinst_inst_Tm (upRen_Tm_Tm xi_Tm) (up_Tm_Tm sigma_Tm)
           (rinstInst_up_Tm_Tm _ _ Eq_Tm) s0)
  | app _ s0 s1 =>
      congr_app (rinst_inst_Tm xi_Tm sigma_Tm Eq_Tm s0)
        (rinst_inst_Tm xi_Tm sigma_Tm Eq_Tm s1)
  | lit _ s0 => congr_lit (eq_refl s0)
  | succ _ s0 => congr_succ (rinst_inst_Tm xi_Tm sigma_Tm Eq_Tm s0)
  | nrec _ s0 s1 s2 =>
      congr_nrec (rinst_inst_Tm xi_Tm sigma_Tm Eq_Tm s0)
        (rinst_inst_Tm xi_Tm sigma_Tm Eq_Tm s1)
        (rinst_inst_Tm (upRen_Tm_Tm xi_Tm) (up_Tm_Tm sigma_Tm)
           (rinstInst_up_Tm_Tm _ _ Eq_Tm) s2)
  | let_ _ s0 s1 =>
      congr_let_ (rinst_inst_Tm xi_Tm sigma_Tm Eq_Tm s0)
        (rinst_inst_Tm (upRen_Tm_Tm xi_Tm) (up_Tm_Tm sigma_Tm)
           (rinstInst_up_Tm_Tm _ _ Eq_Tm) s1)
  end.

Lemma rinstInst'_Tm {m_Tm : nat} {n_Tm : nat} (xi_Tm : fin m_Tm -> fin n_Tm)
  (s : Tm m_Tm) : ren_Tm xi_Tm s = subst_Tm (funcomp (var n_Tm) xi_Tm) s.
Proof.
exact (rinst_inst_Tm xi_Tm _ (fun n => eq_refl) s).
Qed.

Lemma rinstInst'_Tm_pointwise {m_Tm : nat} {n_Tm : nat}
  (xi_Tm : fin m_Tm -> fin n_Tm) :
  pointwise_relation _ eq (ren_Tm xi_Tm)
    (subst_Tm (funcomp (var n_Tm) xi_Tm)).
Proof.
exact (fun s => rinst_inst_Tm xi_Tm _ (fun n => eq_refl) s).
Qed.

Lemma instId'_Tm {m_Tm : nat} (s : Tm m_Tm) : subst_Tm (var m_Tm) s = s.
Proof.
exact (idSubst_Tm (var m_Tm) (fun n => eq_refl) s).
Qed.

Lemma instId'_Tm_pointwise {m_Tm : nat} :
  pointwise_relation _ eq (subst_Tm (var m_Tm)) id.
Proof.
exact (fun s => idSubst_Tm (var m_Tm) (fun n => eq_refl) s).
Qed.

Lemma rinstId'_Tm {m_Tm : nat} (s : Tm m_Tm) : ren_Tm id s = s.
Proof.
exact (eq_ind_r (fun t => t = s) (instId'_Tm s) (rinstInst'_Tm id s)).
Qed.

Lemma rinstId'_Tm_pointwise {m_Tm : nat} :
  pointwise_relation _ eq (@ren_Tm m_Tm m_Tm id) id.
Proof.
exact (fun s => eq_ind_r (fun t => t = s) (instId'_Tm s) (rinstInst'_Tm id s)).
Qed.

Lemma varL'_Tm {m_Tm : nat} {n_Tm : nat} (sigma_Tm : fin m_Tm -> Tm n_Tm)
  (x : fin m_Tm) : subst_Tm sigma_Tm (var m_Tm x) = sigma_Tm x.
Proof.
exact (eq_refl).
Qed.

Lemma varL'_Tm_pointwise {m_Tm : nat} {n_Tm : nat}
  (sigma_Tm : fin m_Tm -> Tm n_Tm) :
  pointwise_relation _ eq (funcomp (subst_Tm sigma_Tm) (var m_Tm)) sigma_Tm.
Proof.
exact (fun x => eq_refl).
Qed.

Lemma varLRen'_Tm {m_Tm : nat} {n_Tm : nat} (xi_Tm : fin m_Tm -> fin n_Tm)
  (x : fin m_Tm) : ren_Tm xi_Tm (var m_Tm x) = var n_Tm (xi_Tm x).
Proof.
exact (eq_refl).
Qed.

Lemma varLRen'_Tm_pointwise {m_Tm : nat} {n_Tm : nat}
  (xi_Tm : fin m_Tm -> fin n_Tm) :
  pointwise_relation _ eq (funcomp (ren_Tm xi_Tm) (var m_Tm))
    (funcomp (var n_Tm) xi_Tm).
Proof.
exact (fun x => eq_refl).
Qed.

Inductive Ty : Type :=
  | Nat : Ty
  | Arr : Ty -> Ty -> Ty.

Lemma congr_Nat : Nat = Nat.
Proof.
exact (eq_refl).
Qed.

Lemma congr_Arr {s0 : Ty} {s1 : Ty} {t0 : Ty} {t1 : Ty} (H0 : s0 = t0)
  (H1 : s1 = t1) : Arr s0 s1 = Arr t0 t1.
Proof.
exact (eq_trans (eq_trans eq_refl (ap (fun x => Arr x s1) H0))
         (ap (fun x => Arr t0 x) H1)).
Qed.

Class Up_Tm X Y :=
    up_Tm : X -> Y.

#[global]
Instance Subst_Tm  {m_Tm n_Tm : nat}: (Subst1 _ _ _) := (@subst_Tm m_Tm n_Tm).

#[global]
Instance Up_Tm_Tm  {m n_Tm : nat}: (Up_Tm _ _) := (@up_Tm_Tm m n_Tm).

#[global]
Instance Ren_Tm  {m_Tm n_Tm : nat}: (Ren1 _ _ _) := (@ren_Tm m_Tm n_Tm).

#[global]
Instance VarInstance_Tm  {n_Tm : nat}: (Var _ _) := (@var n_Tm).

Notation "s [ sigma_Tm ]" := (subst_Tm sigma_Tm s)
( at level 7, left associativity, only printing)  : subst_scope.

Notation "↑__Tm" := up_Tm (only printing)  : subst_scope.

Notation "↑__Tm" := up_Tm_Tm (only printing)  : subst_scope.

Notation "s ⟨ xi_Tm ⟩" := (ren_Tm xi_Tm s)
( at level 7, left associativity, only printing)  : subst_scope.

Notation "'var'" := var ( at level 1, only printing)  : subst_scope.

Notation "x '__Tm'" := (@ids _ _ VarInstance_Tm x)
( at level 5, format "x __Tm", only printing)  : subst_scope.

Notation "x '__Tm'" := (var x) ( at level 5, format "x __Tm")  : subst_scope.

#[global]
Instance subst_Tm_morphism  {m_Tm : nat} {n_Tm : nat}:
 (Proper (respectful (pointwise_relation _ eq) (respectful eq eq))
    (@subst_Tm m_Tm n_Tm)).
Proof.
exact (fun f_Tm g_Tm Eq_Tm s t Eq_st =>
       eq_ind s (fun t' => subst_Tm f_Tm s = subst_Tm g_Tm t')
         (ext_Tm f_Tm g_Tm Eq_Tm s) t Eq_st).
Qed.

#[global]
Instance subst_Tm_morphism2  {m_Tm : nat} {n_Tm : nat}:
 (Proper (respectful (pointwise_relation _ eq) (pointwise_relation _ eq))
    (@subst_Tm m_Tm n_Tm)).
Proof.
exact (fun f_Tm g_Tm Eq_Tm s => ext_Tm f_Tm g_Tm Eq_Tm s).
Qed.

#[global]
Instance ren_Tm_morphism  {m_Tm : nat} {n_Tm : nat}:
 (Proper (respectful (pointwise_relation _ eq) (respectful eq eq))
    (@ren_Tm m_Tm n_Tm)).
Proof.
exact (fun f_Tm g_Tm Eq_Tm s t Eq_st =>
       eq_ind s (fun t' => ren_Tm f_Tm s = ren_Tm g_Tm t')
         (extRen_Tm f_Tm g_Tm Eq_Tm s) t Eq_st).
Qed.

#[global]
Instance ren_Tm_morphism2  {m_Tm : nat} {n_Tm : nat}:
 (Proper (respectful (pointwise_relation _ eq) (pointwise_relation _ eq))
    (@ren_Tm m_Tm n_Tm)).
Proof.
exact (fun f_Tm g_Tm Eq_Tm s => extRen_Tm f_Tm g_Tm Eq_Tm s).
Qed.

Ltac auto_unfold := repeat
                     unfold VarInstance_Tm, Var, ids, Ren_Tm, Ren1, ren1,
                      Up_Tm_Tm, Up_Tm, up_Tm, Subst_Tm, Subst1, subst1.

Tactic Notation "auto_unfold" "in" "*" := repeat
                                           unfold VarInstance_Tm, Var, ids,
                                            Ren_Tm, Ren1, ren1, Up_Tm_Tm,
                                            Up_Tm, up_Tm, Subst_Tm, Subst1,
                                            subst1 in *.

Ltac asimpl' := repeat (first
                 [ progress setoid_rewrite substSubst_Tm_pointwise
                 | progress setoid_rewrite substSubst_Tm
                 | progress setoid_rewrite substRen_Tm_pointwise
                 | progress setoid_rewrite substRen_Tm
                 | progress setoid_rewrite renSubst_Tm_pointwise
                 | progress setoid_rewrite renSubst_Tm
                 | progress setoid_rewrite renRen'_Tm_pointwise
                 | progress setoid_rewrite renRen_Tm
                 | progress setoid_rewrite varLRen'_Tm_pointwise
                 | progress setoid_rewrite varLRen'_Tm
                 | progress setoid_rewrite varL'_Tm_pointwise
                 | progress setoid_rewrite varL'_Tm
                 | progress setoid_rewrite rinstId'_Tm_pointwise
                 | progress setoid_rewrite rinstId'_Tm
                 | progress setoid_rewrite instId'_Tm_pointwise
                 | progress setoid_rewrite instId'_Tm
                 | progress
                    unfold up_list_Tm_Tm, up_Tm_Tm, upRen_list_Tm_Tm,
                     upRen_Tm_Tm, up_ren
                 | progress cbn[subst_Tm ren_Tm]
                 | progress fsimpl ]).

Ltac asimpl := check_no_evars;
                repeat
                 unfold VarInstance_Tm, Var, ids, Ren_Tm, Ren1, ren1,
                  Up_Tm_Tm, Up_Tm, up_Tm, Subst_Tm, Subst1, subst1 in *;
                asimpl'; minimize.

Tactic Notation "asimpl" "in" hyp(J) := revert J; asimpl; intros J.

Tactic Notation "auto_case" := auto_case ltac:(asimpl; cbn; eauto).

Ltac substify := auto_unfold; try setoid_rewrite rinstInst'_Tm_pointwise;
                  try setoid_rewrite rinstInst'_Tm.

Ltac renamify := auto_unfold; try setoid_rewrite_left rinstInst'_Tm_pointwise;
                  try setoid_rewrite_left rinstInst'_Tm.

End Core.

Module Extra.

Import
Core.

Arguments var {n_Tm}.

Arguments let_ {n_Tm}.

Arguments nrec {n_Tm}.

Arguments succ {n_Tm}.

Arguments lit {n_Tm}.

Arguments app {n_Tm}.

Arguments abs {n_Tm}.

#[global] Hint Opaque subst_Tm: rewrite.

#[global] Hint Opaque ren_Tm: rewrite.

End Extra.

Module interface.

Export Core.

Export Extra.

End interface.

Export interface.

