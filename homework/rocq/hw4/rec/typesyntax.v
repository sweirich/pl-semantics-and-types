Require Import core fintype.

Require Import Setoid Morphisms Relation_Definitions.


Module Core.

Inductive Ty (n_Ty : nat) : Type :=
  | var_Ty : fin n_Ty -> Ty n_Ty
  | Void : Ty n_Ty
  | Nat : Ty n_Ty
  | Prod : Ty n_Ty -> Ty n_Ty -> Ty n_Ty
  | Sum : Ty n_Ty -> Ty n_Ty -> Ty n_Ty
  | Arr : Ty n_Ty -> Ty n_Ty -> Ty n_Ty
  | Mu : Ty (S n_Ty) -> Ty n_Ty.

Lemma congr_Void {m_Ty : nat} : Void m_Ty = Void m_Ty.
Proof.
exact (eq_refl).
Qed.

Lemma congr_Nat {m_Ty : nat} : Nat m_Ty = Nat m_Ty.
Proof.
exact (eq_refl).
Qed.

Lemma congr_Prod {m_Ty : nat} {s0 : Ty m_Ty} {s1 : Ty m_Ty} {t0 : Ty m_Ty}
  {t1 : Ty m_Ty} (H0 : s0 = t0) (H1 : s1 = t1) :
  Prod m_Ty s0 s1 = Prod m_Ty t0 t1.
Proof.
exact (eq_trans (eq_trans eq_refl (ap (fun x => Prod m_Ty x s1) H0))
         (ap (fun x => Prod m_Ty t0 x) H1)).
Qed.

Lemma congr_Sum {m_Ty : nat} {s0 : Ty m_Ty} {s1 : Ty m_Ty} {t0 : Ty m_Ty}
  {t1 : Ty m_Ty} (H0 : s0 = t0) (H1 : s1 = t1) :
  Sum m_Ty s0 s1 = Sum m_Ty t0 t1.
Proof.
exact (eq_trans (eq_trans eq_refl (ap (fun x => Sum m_Ty x s1) H0))
         (ap (fun x => Sum m_Ty t0 x) H1)).
Qed.

Lemma congr_Arr {m_Ty : nat} {s0 : Ty m_Ty} {s1 : Ty m_Ty} {t0 : Ty m_Ty}
  {t1 : Ty m_Ty} (H0 : s0 = t0) (H1 : s1 = t1) :
  Arr m_Ty s0 s1 = Arr m_Ty t0 t1.
Proof.
exact (eq_trans (eq_trans eq_refl (ap (fun x => Arr m_Ty x s1) H0))
         (ap (fun x => Arr m_Ty t0 x) H1)).
Qed.

Lemma congr_Mu {m_Ty : nat} {s0 : Ty (S m_Ty)} {t0 : Ty (S m_Ty)}
  (H0 : s0 = t0) : Mu m_Ty s0 = Mu m_Ty t0.
Proof.
exact (eq_trans eq_refl (ap (fun x => Mu m_Ty x) H0)).
Qed.

Lemma upRen_Ty_Ty {m : nat} {n : nat} (xi : fin m -> fin n) :
  fin (S m) -> fin (S n).
Proof.
exact (up_ren xi).
Defined.

Lemma upRen_list_Ty_Ty (p : nat) {m : nat} {n : nat} (xi : fin m -> fin n) :
  fin (plus p m) -> fin (plus p n).
Proof.
exact (upRen_p p xi).
Defined.

Fixpoint ren_Ty {m_Ty : nat} {n_Ty : nat} (xi_Ty : fin m_Ty -> fin n_Ty)
(s : Ty m_Ty) {struct s} : Ty n_Ty :=
  match s with
  | var_Ty _ s0 => var_Ty n_Ty (xi_Ty s0)
  | Void _ => Void n_Ty
  | Nat _ => Nat n_Ty
  | Prod _ s0 s1 => Prod n_Ty (ren_Ty xi_Ty s0) (ren_Ty xi_Ty s1)
  | Sum _ s0 s1 => Sum n_Ty (ren_Ty xi_Ty s0) (ren_Ty xi_Ty s1)
  | Arr _ s0 s1 => Arr n_Ty (ren_Ty xi_Ty s0) (ren_Ty xi_Ty s1)
  | Mu _ s0 => Mu n_Ty (ren_Ty (upRen_Ty_Ty xi_Ty) s0)
  end.

Lemma up_Ty_Ty {m : nat} {n_Ty : nat} (sigma : fin m -> Ty n_Ty) :
  fin (S m) -> Ty (S n_Ty).
Proof.
exact (scons (var_Ty (S n_Ty) var_zero) (funcomp (ren_Ty shift) sigma)).
Defined.

Lemma up_list_Ty_Ty (p : nat) {m : nat} {n_Ty : nat}
  (sigma : fin m -> Ty n_Ty) : fin (plus p m) -> Ty (plus p n_Ty).
Proof.
exact (scons_p p (funcomp (var_Ty (plus p n_Ty)) (zero_p p))
         (funcomp (ren_Ty (shift_p p)) sigma)).
Defined.

Fixpoint subst_Ty {m_Ty : nat} {n_Ty : nat} (sigma_Ty : fin m_Ty -> Ty n_Ty)
(s : Ty m_Ty) {struct s} : Ty n_Ty :=
  match s with
  | var_Ty _ s0 => sigma_Ty s0
  | Void _ => Void n_Ty
  | Nat _ => Nat n_Ty
  | Prod _ s0 s1 => Prod n_Ty (subst_Ty sigma_Ty s0) (subst_Ty sigma_Ty s1)
  | Sum _ s0 s1 => Sum n_Ty (subst_Ty sigma_Ty s0) (subst_Ty sigma_Ty s1)
  | Arr _ s0 s1 => Arr n_Ty (subst_Ty sigma_Ty s0) (subst_Ty sigma_Ty s1)
  | Mu _ s0 => Mu n_Ty (subst_Ty (up_Ty_Ty sigma_Ty) s0)
  end.

Lemma upId_Ty_Ty {m_Ty : nat} (sigma : fin m_Ty -> Ty m_Ty)
  (Eq : forall x, sigma x = var_Ty m_Ty x) :
  forall x, up_Ty_Ty sigma x = var_Ty (S m_Ty) x.
Proof.
exact (fun n =>
       match n with
       | Some fin_n => ap (ren_Ty shift) (Eq fin_n)
       | None => eq_refl
       end).
Qed.

Lemma upId_list_Ty_Ty {p : nat} {m_Ty : nat} (sigma : fin m_Ty -> Ty m_Ty)
  (Eq : forall x, sigma x = var_Ty m_Ty x) :
  forall x, up_list_Ty_Ty p sigma x = var_Ty (plus p m_Ty) x.
Proof.
exact (fun n =>
       scons_p_eta (var_Ty (plus p m_Ty))
         (fun n => ap (ren_Ty (shift_p p)) (Eq n)) (fun n => eq_refl)).
Qed.

Fixpoint idSubst_Ty {m_Ty : nat} (sigma_Ty : fin m_Ty -> Ty m_Ty)
(Eq_Ty : forall x, sigma_Ty x = var_Ty m_Ty x) (s : Ty m_Ty) {struct s} :
subst_Ty sigma_Ty s = s :=
  match s with
  | var_Ty _ s0 => Eq_Ty s0
  | Void _ => congr_Void
  | Nat _ => congr_Nat
  | Prod _ s0 s1 =>
      congr_Prod (idSubst_Ty sigma_Ty Eq_Ty s0)
        (idSubst_Ty sigma_Ty Eq_Ty s1)
  | Sum _ s0 s1 =>
      congr_Sum (idSubst_Ty sigma_Ty Eq_Ty s0) (idSubst_Ty sigma_Ty Eq_Ty s1)
  | Arr _ s0 s1 =>
      congr_Arr (idSubst_Ty sigma_Ty Eq_Ty s0) (idSubst_Ty sigma_Ty Eq_Ty s1)
  | Mu _ s0 =>
      congr_Mu (idSubst_Ty (up_Ty_Ty sigma_Ty) (upId_Ty_Ty _ Eq_Ty) s0)
  end.

Lemma upExtRen_Ty_Ty {m : nat} {n : nat} (xi : fin m -> fin n)
  (zeta : fin m -> fin n) (Eq : forall x, xi x = zeta x) :
  forall x, upRen_Ty_Ty xi x = upRen_Ty_Ty zeta x.
Proof.
exact (fun n =>
       match n with
       | Some fin_n => ap shift (Eq fin_n)
       | None => eq_refl
       end).
Qed.

Lemma upExtRen_list_Ty_Ty {p : nat} {m : nat} {n : nat} (xi : fin m -> fin n)
  (zeta : fin m -> fin n) (Eq : forall x, xi x = zeta x) :
  forall x, upRen_list_Ty_Ty p xi x = upRen_list_Ty_Ty p zeta x.
Proof.
exact (fun n =>
       scons_p_congr (fun n => eq_refl) (fun n => ap (shift_p p) (Eq n))).
Qed.

Fixpoint extRen_Ty {m_Ty : nat} {n_Ty : nat} (xi_Ty : fin m_Ty -> fin n_Ty)
(zeta_Ty : fin m_Ty -> fin n_Ty) (Eq_Ty : forall x, xi_Ty x = zeta_Ty x)
(s : Ty m_Ty) {struct s} : ren_Ty xi_Ty s = ren_Ty zeta_Ty s :=
  match s with
  | var_Ty _ s0 => ap (var_Ty n_Ty) (Eq_Ty s0)
  | Void _ => congr_Void
  | Nat _ => congr_Nat
  | Prod _ s0 s1 =>
      congr_Prod (extRen_Ty xi_Ty zeta_Ty Eq_Ty s0)
        (extRen_Ty xi_Ty zeta_Ty Eq_Ty s1)
  | Sum _ s0 s1 =>
      congr_Sum (extRen_Ty xi_Ty zeta_Ty Eq_Ty s0)
        (extRen_Ty xi_Ty zeta_Ty Eq_Ty s1)
  | Arr _ s0 s1 =>
      congr_Arr (extRen_Ty xi_Ty zeta_Ty Eq_Ty s0)
        (extRen_Ty xi_Ty zeta_Ty Eq_Ty s1)
  | Mu _ s0 =>
      congr_Mu
        (extRen_Ty (upRen_Ty_Ty xi_Ty) (upRen_Ty_Ty zeta_Ty)
           (upExtRen_Ty_Ty _ _ Eq_Ty) s0)
  end.

Lemma upExt_Ty_Ty {m : nat} {n_Ty : nat} (sigma : fin m -> Ty n_Ty)
  (tau : fin m -> Ty n_Ty) (Eq : forall x, sigma x = tau x) :
  forall x, up_Ty_Ty sigma x = up_Ty_Ty tau x.
Proof.
exact (fun n =>
       match n with
       | Some fin_n => ap (ren_Ty shift) (Eq fin_n)
       | None => eq_refl
       end).
Qed.

Lemma upExt_list_Ty_Ty {p : nat} {m : nat} {n_Ty : nat}
  (sigma : fin m -> Ty n_Ty) (tau : fin m -> Ty n_Ty)
  (Eq : forall x, sigma x = tau x) :
  forall x, up_list_Ty_Ty p sigma x = up_list_Ty_Ty p tau x.
Proof.
exact (fun n =>
       scons_p_congr (fun n => eq_refl)
         (fun n => ap (ren_Ty (shift_p p)) (Eq n))).
Qed.

Fixpoint ext_Ty {m_Ty : nat} {n_Ty : nat} (sigma_Ty : fin m_Ty -> Ty n_Ty)
(tau_Ty : fin m_Ty -> Ty n_Ty) (Eq_Ty : forall x, sigma_Ty x = tau_Ty x)
(s : Ty m_Ty) {struct s} : subst_Ty sigma_Ty s = subst_Ty tau_Ty s :=
  match s with
  | var_Ty _ s0 => Eq_Ty s0
  | Void _ => congr_Void
  | Nat _ => congr_Nat
  | Prod _ s0 s1 =>
      congr_Prod (ext_Ty sigma_Ty tau_Ty Eq_Ty s0)
        (ext_Ty sigma_Ty tau_Ty Eq_Ty s1)
  | Sum _ s0 s1 =>
      congr_Sum (ext_Ty sigma_Ty tau_Ty Eq_Ty s0)
        (ext_Ty sigma_Ty tau_Ty Eq_Ty s1)
  | Arr _ s0 s1 =>
      congr_Arr (ext_Ty sigma_Ty tau_Ty Eq_Ty s0)
        (ext_Ty sigma_Ty tau_Ty Eq_Ty s1)
  | Mu _ s0 =>
      congr_Mu
        (ext_Ty (up_Ty_Ty sigma_Ty) (up_Ty_Ty tau_Ty) (upExt_Ty_Ty _ _ Eq_Ty)
           s0)
  end.

Lemma up_ren_ren_Ty_Ty {k : nat} {l : nat} {m : nat} (xi : fin k -> fin l)
  (zeta : fin l -> fin m) (rho : fin k -> fin m)
  (Eq : forall x, funcomp zeta xi x = rho x) :
  forall x, funcomp (upRen_Ty_Ty zeta) (upRen_Ty_Ty xi) x = upRen_Ty_Ty rho x.
Proof.
exact (up_ren_ren xi zeta rho Eq).
Qed.

Lemma up_ren_ren_list_Ty_Ty {p : nat} {k : nat} {l : nat} {m : nat}
  (xi : fin k -> fin l) (zeta : fin l -> fin m) (rho : fin k -> fin m)
  (Eq : forall x, funcomp zeta xi x = rho x) :
  forall x,
  funcomp (upRen_list_Ty_Ty p zeta) (upRen_list_Ty_Ty p xi) x =
  upRen_list_Ty_Ty p rho x.
Proof.
exact (up_ren_ren_p Eq).
Qed.

Fixpoint compRenRen_Ty {k_Ty : nat} {l_Ty : nat} {m_Ty : nat}
(xi_Ty : fin m_Ty -> fin k_Ty) (zeta_Ty : fin k_Ty -> fin l_Ty)
(rho_Ty : fin m_Ty -> fin l_Ty)
(Eq_Ty : forall x, funcomp zeta_Ty xi_Ty x = rho_Ty x) (s : Ty m_Ty) {struct
 s} :
ren_Ty zeta_Ty (ren_Ty xi_Ty s) = ren_Ty rho_Ty s :=
  match s with
  | var_Ty _ s0 => ap (var_Ty l_Ty) (Eq_Ty s0)
  | Void _ => congr_Void
  | Nat _ => congr_Nat
  | Prod _ s0 s1 =>
      congr_Prod (compRenRen_Ty xi_Ty zeta_Ty rho_Ty Eq_Ty s0)
        (compRenRen_Ty xi_Ty zeta_Ty rho_Ty Eq_Ty s1)
  | Sum _ s0 s1 =>
      congr_Sum (compRenRen_Ty xi_Ty zeta_Ty rho_Ty Eq_Ty s0)
        (compRenRen_Ty xi_Ty zeta_Ty rho_Ty Eq_Ty s1)
  | Arr _ s0 s1 =>
      congr_Arr (compRenRen_Ty xi_Ty zeta_Ty rho_Ty Eq_Ty s0)
        (compRenRen_Ty xi_Ty zeta_Ty rho_Ty Eq_Ty s1)
  | Mu _ s0 =>
      congr_Mu
        (compRenRen_Ty (upRen_Ty_Ty xi_Ty) (upRen_Ty_Ty zeta_Ty)
           (upRen_Ty_Ty rho_Ty) (up_ren_ren _ _ _ Eq_Ty) s0)
  end.

Lemma up_ren_subst_Ty_Ty {k : nat} {l : nat} {m_Ty : nat}
  (xi : fin k -> fin l) (tau : fin l -> Ty m_Ty) (theta : fin k -> Ty m_Ty)
  (Eq : forall x, funcomp tau xi x = theta x) :
  forall x, funcomp (up_Ty_Ty tau) (upRen_Ty_Ty xi) x = up_Ty_Ty theta x.
Proof.
exact (fun n =>
       match n with
       | Some fin_n => ap (ren_Ty shift) (Eq fin_n)
       | None => eq_refl
       end).
Qed.

Lemma up_ren_subst_list_Ty_Ty {p : nat} {k : nat} {l : nat} {m_Ty : nat}
  (xi : fin k -> fin l) (tau : fin l -> Ty m_Ty) (theta : fin k -> Ty m_Ty)
  (Eq : forall x, funcomp tau xi x = theta x) :
  forall x,
  funcomp (up_list_Ty_Ty p tau) (upRen_list_Ty_Ty p xi) x =
  up_list_Ty_Ty p theta x.
Proof.
exact (fun n =>
       eq_trans (scons_p_comp' _ _ _ n)
         (scons_p_congr (fun z => scons_p_head' _ _ z)
            (fun z =>
             eq_trans (scons_p_tail' _ _ (xi z))
               (ap (ren_Ty (shift_p p)) (Eq z))))).
Qed.

Fixpoint compRenSubst_Ty {k_Ty : nat} {l_Ty : nat} {m_Ty : nat}
(xi_Ty : fin m_Ty -> fin k_Ty) (tau_Ty : fin k_Ty -> Ty l_Ty)
(theta_Ty : fin m_Ty -> Ty l_Ty)
(Eq_Ty : forall x, funcomp tau_Ty xi_Ty x = theta_Ty x) (s : Ty m_Ty) {struct
 s} :
subst_Ty tau_Ty (ren_Ty xi_Ty s) = subst_Ty theta_Ty s :=
  match s with
  | var_Ty _ s0 => Eq_Ty s0
  | Void _ => congr_Void
  | Nat _ => congr_Nat
  | Prod _ s0 s1 =>
      congr_Prod (compRenSubst_Ty xi_Ty tau_Ty theta_Ty Eq_Ty s0)
        (compRenSubst_Ty xi_Ty tau_Ty theta_Ty Eq_Ty s1)
  | Sum _ s0 s1 =>
      congr_Sum (compRenSubst_Ty xi_Ty tau_Ty theta_Ty Eq_Ty s0)
        (compRenSubst_Ty xi_Ty tau_Ty theta_Ty Eq_Ty s1)
  | Arr _ s0 s1 =>
      congr_Arr (compRenSubst_Ty xi_Ty tau_Ty theta_Ty Eq_Ty s0)
        (compRenSubst_Ty xi_Ty tau_Ty theta_Ty Eq_Ty s1)
  | Mu _ s0 =>
      congr_Mu
        (compRenSubst_Ty (upRen_Ty_Ty xi_Ty) (up_Ty_Ty tau_Ty)
           (up_Ty_Ty theta_Ty) (up_ren_subst_Ty_Ty _ _ _ Eq_Ty) s0)
  end.

Lemma up_subst_ren_Ty_Ty {k : nat} {l_Ty : nat} {m_Ty : nat}
  (sigma : fin k -> Ty l_Ty) (zeta_Ty : fin l_Ty -> fin m_Ty)
  (theta : fin k -> Ty m_Ty)
  (Eq : forall x, funcomp (ren_Ty zeta_Ty) sigma x = theta x) :
  forall x,
  funcomp (ren_Ty (upRen_Ty_Ty zeta_Ty)) (up_Ty_Ty sigma) x =
  up_Ty_Ty theta x.
Proof.
exact (fun n =>
       match n with
       | Some fin_n =>
           eq_trans
             (compRenRen_Ty shift (upRen_Ty_Ty zeta_Ty)
                (funcomp shift zeta_Ty) (fun x => eq_refl) (sigma fin_n))
             (eq_trans
                (eq_sym
                   (compRenRen_Ty zeta_Ty shift (funcomp shift zeta_Ty)
                      (fun x => eq_refl) (sigma fin_n)))
                (ap (ren_Ty shift) (Eq fin_n)))
       | None => eq_refl
       end).
Qed.

Lemma up_subst_ren_list_Ty_Ty {p : nat} {k : nat} {l_Ty : nat} {m_Ty : nat}
  (sigma : fin k -> Ty l_Ty) (zeta_Ty : fin l_Ty -> fin m_Ty)
  (theta : fin k -> Ty m_Ty)
  (Eq : forall x, funcomp (ren_Ty zeta_Ty) sigma x = theta x) :
  forall x,
  funcomp (ren_Ty (upRen_list_Ty_Ty p zeta_Ty)) (up_list_Ty_Ty p sigma) x =
  up_list_Ty_Ty p theta x.
Proof.
exact (fun n =>
       eq_trans (scons_p_comp' _ _ _ n)
         (scons_p_congr
            (fun x => ap (var_Ty (plus p m_Ty)) (scons_p_head' _ _ x))
            (fun n =>
             eq_trans
               (compRenRen_Ty (shift_p p) (upRen_list_Ty_Ty p zeta_Ty)
                  (funcomp (shift_p p) zeta_Ty)
                  (fun x => scons_p_tail' _ _ x) (sigma n))
               (eq_trans
                  (eq_sym
                     (compRenRen_Ty zeta_Ty (shift_p p)
                        (funcomp (shift_p p) zeta_Ty) (fun x => eq_refl)
                        (sigma n)))
                  (ap (ren_Ty (shift_p p)) (Eq n)))))).
Qed.

Fixpoint compSubstRen_Ty {k_Ty : nat} {l_Ty : nat} {m_Ty : nat}
(sigma_Ty : fin m_Ty -> Ty k_Ty) (zeta_Ty : fin k_Ty -> fin l_Ty)
(theta_Ty : fin m_Ty -> Ty l_Ty)
(Eq_Ty : forall x, funcomp (ren_Ty zeta_Ty) sigma_Ty x = theta_Ty x)
(s : Ty m_Ty) {struct s} :
ren_Ty zeta_Ty (subst_Ty sigma_Ty s) = subst_Ty theta_Ty s :=
  match s with
  | var_Ty _ s0 => Eq_Ty s0
  | Void _ => congr_Void
  | Nat _ => congr_Nat
  | Prod _ s0 s1 =>
      congr_Prod (compSubstRen_Ty sigma_Ty zeta_Ty theta_Ty Eq_Ty s0)
        (compSubstRen_Ty sigma_Ty zeta_Ty theta_Ty Eq_Ty s1)
  | Sum _ s0 s1 =>
      congr_Sum (compSubstRen_Ty sigma_Ty zeta_Ty theta_Ty Eq_Ty s0)
        (compSubstRen_Ty sigma_Ty zeta_Ty theta_Ty Eq_Ty s1)
  | Arr _ s0 s1 =>
      congr_Arr (compSubstRen_Ty sigma_Ty zeta_Ty theta_Ty Eq_Ty s0)
        (compSubstRen_Ty sigma_Ty zeta_Ty theta_Ty Eq_Ty s1)
  | Mu _ s0 =>
      congr_Mu
        (compSubstRen_Ty (up_Ty_Ty sigma_Ty) (upRen_Ty_Ty zeta_Ty)
           (up_Ty_Ty theta_Ty) (up_subst_ren_Ty_Ty _ _ _ Eq_Ty) s0)
  end.

Lemma up_subst_subst_Ty_Ty {k : nat} {l_Ty : nat} {m_Ty : nat}
  (sigma : fin k -> Ty l_Ty) (tau_Ty : fin l_Ty -> Ty m_Ty)
  (theta : fin k -> Ty m_Ty)
  (Eq : forall x, funcomp (subst_Ty tau_Ty) sigma x = theta x) :
  forall x,
  funcomp (subst_Ty (up_Ty_Ty tau_Ty)) (up_Ty_Ty sigma) x = up_Ty_Ty theta x.
Proof.
exact (fun n =>
       match n with
       | Some fin_n =>
           eq_trans
             (compRenSubst_Ty shift (up_Ty_Ty tau_Ty)
                (funcomp (up_Ty_Ty tau_Ty) shift) (fun x => eq_refl)
                (sigma fin_n))
             (eq_trans
                (eq_sym
                   (compSubstRen_Ty tau_Ty shift
                      (funcomp (ren_Ty shift) tau_Ty) (fun x => eq_refl)
                      (sigma fin_n)))
                (ap (ren_Ty shift) (Eq fin_n)))
       | None => eq_refl
       end).
Qed.

Lemma up_subst_subst_list_Ty_Ty {p : nat} {k : nat} {l_Ty : nat} {m_Ty : nat}
  (sigma : fin k -> Ty l_Ty) (tau_Ty : fin l_Ty -> Ty m_Ty)
  (theta : fin k -> Ty m_Ty)
  (Eq : forall x, funcomp (subst_Ty tau_Ty) sigma x = theta x) :
  forall x,
  funcomp (subst_Ty (up_list_Ty_Ty p tau_Ty)) (up_list_Ty_Ty p sigma) x =
  up_list_Ty_Ty p theta x.
Proof.
exact (fun n =>
       eq_trans
         (scons_p_comp' (funcomp (var_Ty (plus p l_Ty)) (zero_p p)) _ _ n)
         (scons_p_congr
            (fun x => scons_p_head' _ (fun z => ren_Ty (shift_p p) _) x)
            (fun n =>
             eq_trans
               (compRenSubst_Ty (shift_p p) (up_list_Ty_Ty p tau_Ty)
                  (funcomp (up_list_Ty_Ty p tau_Ty) (shift_p p))
                  (fun x => eq_refl) (sigma n))
               (eq_trans
                  (eq_sym
                     (compSubstRen_Ty tau_Ty (shift_p p) _
                        (fun x => eq_sym (scons_p_tail' _ _ x)) (sigma n)))
                  (ap (ren_Ty (shift_p p)) (Eq n)))))).
Qed.

Fixpoint compSubstSubst_Ty {k_Ty : nat} {l_Ty : nat} {m_Ty : nat}
(sigma_Ty : fin m_Ty -> Ty k_Ty) (tau_Ty : fin k_Ty -> Ty l_Ty)
(theta_Ty : fin m_Ty -> Ty l_Ty)
(Eq_Ty : forall x, funcomp (subst_Ty tau_Ty) sigma_Ty x = theta_Ty x)
(s : Ty m_Ty) {struct s} :
subst_Ty tau_Ty (subst_Ty sigma_Ty s) = subst_Ty theta_Ty s :=
  match s with
  | var_Ty _ s0 => Eq_Ty s0
  | Void _ => congr_Void
  | Nat _ => congr_Nat
  | Prod _ s0 s1 =>
      congr_Prod (compSubstSubst_Ty sigma_Ty tau_Ty theta_Ty Eq_Ty s0)
        (compSubstSubst_Ty sigma_Ty tau_Ty theta_Ty Eq_Ty s1)
  | Sum _ s0 s1 =>
      congr_Sum (compSubstSubst_Ty sigma_Ty tau_Ty theta_Ty Eq_Ty s0)
        (compSubstSubst_Ty sigma_Ty tau_Ty theta_Ty Eq_Ty s1)
  | Arr _ s0 s1 =>
      congr_Arr (compSubstSubst_Ty sigma_Ty tau_Ty theta_Ty Eq_Ty s0)
        (compSubstSubst_Ty sigma_Ty tau_Ty theta_Ty Eq_Ty s1)
  | Mu _ s0 =>
      congr_Mu
        (compSubstSubst_Ty (up_Ty_Ty sigma_Ty) (up_Ty_Ty tau_Ty)
           (up_Ty_Ty theta_Ty) (up_subst_subst_Ty_Ty _ _ _ Eq_Ty) s0)
  end.

Lemma renRen_Ty {k_Ty : nat} {l_Ty : nat} {m_Ty : nat}
  (xi_Ty : fin m_Ty -> fin k_Ty) (zeta_Ty : fin k_Ty -> fin l_Ty)
  (s : Ty m_Ty) :
  ren_Ty zeta_Ty (ren_Ty xi_Ty s) = ren_Ty (funcomp zeta_Ty xi_Ty) s.
Proof.
exact (compRenRen_Ty xi_Ty zeta_Ty _ (fun n => eq_refl) s).
Qed.

Lemma renRen'_Ty_pointwise {k_Ty : nat} {l_Ty : nat} {m_Ty : nat}
  (xi_Ty : fin m_Ty -> fin k_Ty) (zeta_Ty : fin k_Ty -> fin l_Ty) :
  pointwise_relation _ eq (funcomp (ren_Ty zeta_Ty) (ren_Ty xi_Ty))
    (ren_Ty (funcomp zeta_Ty xi_Ty)).
Proof.
exact (fun s => compRenRen_Ty xi_Ty zeta_Ty _ (fun n => eq_refl) s).
Qed.

Lemma renSubst_Ty {k_Ty : nat} {l_Ty : nat} {m_Ty : nat}
  (xi_Ty : fin m_Ty -> fin k_Ty) (tau_Ty : fin k_Ty -> Ty l_Ty) (s : Ty m_Ty)
  : subst_Ty tau_Ty (ren_Ty xi_Ty s) = subst_Ty (funcomp tau_Ty xi_Ty) s.
Proof.
exact (compRenSubst_Ty xi_Ty tau_Ty _ (fun n => eq_refl) s).
Qed.

Lemma renSubst_Ty_pointwise {k_Ty : nat} {l_Ty : nat} {m_Ty : nat}
  (xi_Ty : fin m_Ty -> fin k_Ty) (tau_Ty : fin k_Ty -> Ty l_Ty) :
  pointwise_relation _ eq (funcomp (subst_Ty tau_Ty) (ren_Ty xi_Ty))
    (subst_Ty (funcomp tau_Ty xi_Ty)).
Proof.
exact (fun s => compRenSubst_Ty xi_Ty tau_Ty _ (fun n => eq_refl) s).
Qed.

Lemma substRen_Ty {k_Ty : nat} {l_Ty : nat} {m_Ty : nat}
  (sigma_Ty : fin m_Ty -> Ty k_Ty) (zeta_Ty : fin k_Ty -> fin l_Ty)
  (s : Ty m_Ty) :
  ren_Ty zeta_Ty (subst_Ty sigma_Ty s) =
  subst_Ty (funcomp (ren_Ty zeta_Ty) sigma_Ty) s.
Proof.
exact (compSubstRen_Ty sigma_Ty zeta_Ty _ (fun n => eq_refl) s).
Qed.

Lemma substRen_Ty_pointwise {k_Ty : nat} {l_Ty : nat} {m_Ty : nat}
  (sigma_Ty : fin m_Ty -> Ty k_Ty) (zeta_Ty : fin k_Ty -> fin l_Ty) :
  pointwise_relation _ eq (funcomp (ren_Ty zeta_Ty) (subst_Ty sigma_Ty))
    (subst_Ty (funcomp (ren_Ty zeta_Ty) sigma_Ty)).
Proof.
exact (fun s => compSubstRen_Ty sigma_Ty zeta_Ty _ (fun n => eq_refl) s).
Qed.

Lemma substSubst_Ty {k_Ty : nat} {l_Ty : nat} {m_Ty : nat}
  (sigma_Ty : fin m_Ty -> Ty k_Ty) (tau_Ty : fin k_Ty -> Ty l_Ty)
  (s : Ty m_Ty) :
  subst_Ty tau_Ty (subst_Ty sigma_Ty s) =
  subst_Ty (funcomp (subst_Ty tau_Ty) sigma_Ty) s.
Proof.
exact (compSubstSubst_Ty sigma_Ty tau_Ty _ (fun n => eq_refl) s).
Qed.

Lemma substSubst_Ty_pointwise {k_Ty : nat} {l_Ty : nat} {m_Ty : nat}
  (sigma_Ty : fin m_Ty -> Ty k_Ty) (tau_Ty : fin k_Ty -> Ty l_Ty) :
  pointwise_relation _ eq (funcomp (subst_Ty tau_Ty) (subst_Ty sigma_Ty))
    (subst_Ty (funcomp (subst_Ty tau_Ty) sigma_Ty)).
Proof.
exact (fun s => compSubstSubst_Ty sigma_Ty tau_Ty _ (fun n => eq_refl) s).
Qed.

Lemma rinstInst_up_Ty_Ty {m : nat} {n_Ty : nat} (xi : fin m -> fin n_Ty)
  (sigma : fin m -> Ty n_Ty)
  (Eq : forall x, funcomp (var_Ty n_Ty) xi x = sigma x) :
  forall x, funcomp (var_Ty (S n_Ty)) (upRen_Ty_Ty xi) x = up_Ty_Ty sigma x.
Proof.
exact (fun n =>
       match n with
       | Some fin_n => ap (ren_Ty shift) (Eq fin_n)
       | None => eq_refl
       end).
Qed.

Lemma rinstInst_up_list_Ty_Ty {p : nat} {m : nat} {n_Ty : nat}
  (xi : fin m -> fin n_Ty) (sigma : fin m -> Ty n_Ty)
  (Eq : forall x, funcomp (var_Ty n_Ty) xi x = sigma x) :
  forall x,
  funcomp (var_Ty (plus p n_Ty)) (upRen_list_Ty_Ty p xi) x =
  up_list_Ty_Ty p sigma x.
Proof.
exact (fun n =>
       eq_trans (scons_p_comp' _ _ (var_Ty (plus p n_Ty)) n)
         (scons_p_congr (fun z => eq_refl)
            (fun n => ap (ren_Ty (shift_p p)) (Eq n)))).
Qed.

Fixpoint rinst_inst_Ty {m_Ty : nat} {n_Ty : nat}
(xi_Ty : fin m_Ty -> fin n_Ty) (sigma_Ty : fin m_Ty -> Ty n_Ty)
(Eq_Ty : forall x, funcomp (var_Ty n_Ty) xi_Ty x = sigma_Ty x) (s : Ty m_Ty)
{struct s} : ren_Ty xi_Ty s = subst_Ty sigma_Ty s :=
  match s with
  | var_Ty _ s0 => Eq_Ty s0
  | Void _ => congr_Void
  | Nat _ => congr_Nat
  | Prod _ s0 s1 =>
      congr_Prod (rinst_inst_Ty xi_Ty sigma_Ty Eq_Ty s0)
        (rinst_inst_Ty xi_Ty sigma_Ty Eq_Ty s1)
  | Sum _ s0 s1 =>
      congr_Sum (rinst_inst_Ty xi_Ty sigma_Ty Eq_Ty s0)
        (rinst_inst_Ty xi_Ty sigma_Ty Eq_Ty s1)
  | Arr _ s0 s1 =>
      congr_Arr (rinst_inst_Ty xi_Ty sigma_Ty Eq_Ty s0)
        (rinst_inst_Ty xi_Ty sigma_Ty Eq_Ty s1)
  | Mu _ s0 =>
      congr_Mu
        (rinst_inst_Ty (upRen_Ty_Ty xi_Ty) (up_Ty_Ty sigma_Ty)
           (rinstInst_up_Ty_Ty _ _ Eq_Ty) s0)
  end.

Lemma rinstInst'_Ty {m_Ty : nat} {n_Ty : nat} (xi_Ty : fin m_Ty -> fin n_Ty)
  (s : Ty m_Ty) : ren_Ty xi_Ty s = subst_Ty (funcomp (var_Ty n_Ty) xi_Ty) s.
Proof.
exact (rinst_inst_Ty xi_Ty _ (fun n => eq_refl) s).
Qed.

Lemma rinstInst'_Ty_pointwise {m_Ty : nat} {n_Ty : nat}
  (xi_Ty : fin m_Ty -> fin n_Ty) :
  pointwise_relation _ eq (ren_Ty xi_Ty)
    (subst_Ty (funcomp (var_Ty n_Ty) xi_Ty)).
Proof.
exact (fun s => rinst_inst_Ty xi_Ty _ (fun n => eq_refl) s).
Qed.

Lemma instId'_Ty {m_Ty : nat} (s : Ty m_Ty) : subst_Ty (var_Ty m_Ty) s = s.
Proof.
exact (idSubst_Ty (var_Ty m_Ty) (fun n => eq_refl) s).
Qed.

Lemma instId'_Ty_pointwise {m_Ty : nat} :
  pointwise_relation _ eq (subst_Ty (var_Ty m_Ty)) id.
Proof.
exact (fun s => idSubst_Ty (var_Ty m_Ty) (fun n => eq_refl) s).
Qed.

Lemma rinstId'_Ty {m_Ty : nat} (s : Ty m_Ty) : ren_Ty id s = s.
Proof.
exact (eq_ind_r (fun t => t = s) (instId'_Ty s) (rinstInst'_Ty id s)).
Qed.

Lemma rinstId'_Ty_pointwise {m_Ty : nat} :
  pointwise_relation _ eq (@ren_Ty m_Ty m_Ty id) id.
Proof.
exact (fun s => eq_ind_r (fun t => t = s) (instId'_Ty s) (rinstInst'_Ty id s)).
Qed.

Lemma varL'_Ty {m_Ty : nat} {n_Ty : nat} (sigma_Ty : fin m_Ty -> Ty n_Ty)
  (x : fin m_Ty) : subst_Ty sigma_Ty (var_Ty m_Ty x) = sigma_Ty x.
Proof.
exact (eq_refl).
Qed.

Lemma varL'_Ty_pointwise {m_Ty : nat} {n_Ty : nat}
  (sigma_Ty : fin m_Ty -> Ty n_Ty) :
  pointwise_relation _ eq (funcomp (subst_Ty sigma_Ty) (var_Ty m_Ty))
    sigma_Ty.
Proof.
exact (fun x => eq_refl).
Qed.

Lemma varLRen'_Ty {m_Ty : nat} {n_Ty : nat} (xi_Ty : fin m_Ty -> fin n_Ty)
  (x : fin m_Ty) : ren_Ty xi_Ty (var_Ty m_Ty x) = var_Ty n_Ty (xi_Ty x).
Proof.
exact (eq_refl).
Qed.

Lemma varLRen'_Ty_pointwise {m_Ty : nat} {n_Ty : nat}
  (xi_Ty : fin m_Ty -> fin n_Ty) :
  pointwise_relation _ eq (funcomp (ren_Ty xi_Ty) (var_Ty m_Ty))
    (funcomp (var_Ty n_Ty) xi_Ty).
Proof.
exact (fun x => eq_refl).
Qed.

Class Up_Ty X Y :=
    up_Ty : X -> Y.

#[global]
Instance Subst_Ty  {m_Ty n_Ty : nat}: (Subst1 _ _ _) := (@subst_Ty m_Ty n_Ty).

#[global]
Instance Up_Ty_Ty  {m n_Ty : nat}: (Up_Ty _ _) := (@up_Ty_Ty m n_Ty).

#[global]
Instance Ren_Ty  {m_Ty n_Ty : nat}: (Ren1 _ _ _) := (@ren_Ty m_Ty n_Ty).

#[global]
Instance VarInstance_Ty  {n_Ty : nat}: (Var _ _) := (@var_Ty n_Ty).

Notation "s [ sigma_Ty ]" := (subst_Ty sigma_Ty s)
( at level 7, left associativity, only printing)  : subst_scope.

Notation "↑__Ty" := up_Ty (only printing)  : subst_scope.

Notation "↑__Ty" := up_Ty_Ty (only printing)  : subst_scope.

Notation "s ⟨ xi_Ty ⟩" := (ren_Ty xi_Ty s)
( at level 7, left associativity, only printing)  : subst_scope.

Notation "'var'" := var_Ty ( at level 1, only printing)  : subst_scope.

Notation "x '__Ty'" := (@ids _ _ VarInstance_Ty x)
( at level 5, format "x __Ty", only printing)  : subst_scope.

Notation "x '__Ty'" := (var_Ty x) ( at level 5, format "x __Ty")  :
subst_scope.

#[global]
Instance subst_Ty_morphism  {m_Ty : nat} {n_Ty : nat}:
 (Proper (respectful (pointwise_relation _ eq) (respectful eq eq))
    (@subst_Ty m_Ty n_Ty)).
Proof.
exact (fun f_Ty g_Ty Eq_Ty s t Eq_st =>
       eq_ind s (fun t' => subst_Ty f_Ty s = subst_Ty g_Ty t')
         (ext_Ty f_Ty g_Ty Eq_Ty s) t Eq_st).
Qed.

#[global]
Instance subst_Ty_morphism2  {m_Ty : nat} {n_Ty : nat}:
 (Proper (respectful (pointwise_relation _ eq) (pointwise_relation _ eq))
    (@subst_Ty m_Ty n_Ty)).
Proof.
exact (fun f_Ty g_Ty Eq_Ty s => ext_Ty f_Ty g_Ty Eq_Ty s).
Qed.

#[global]
Instance ren_Ty_morphism  {m_Ty : nat} {n_Ty : nat}:
 (Proper (respectful (pointwise_relation _ eq) (respectful eq eq))
    (@ren_Ty m_Ty n_Ty)).
Proof.
exact (fun f_Ty g_Ty Eq_Ty s t Eq_st =>
       eq_ind s (fun t' => ren_Ty f_Ty s = ren_Ty g_Ty t')
         (extRen_Ty f_Ty g_Ty Eq_Ty s) t Eq_st).
Qed.

#[global]
Instance ren_Ty_morphism2  {m_Ty : nat} {n_Ty : nat}:
 (Proper (respectful (pointwise_relation _ eq) (pointwise_relation _ eq))
    (@ren_Ty m_Ty n_Ty)).
Proof.
exact (fun f_Ty g_Ty Eq_Ty s => extRen_Ty f_Ty g_Ty Eq_Ty s).
Qed.

Ltac auto_unfold := repeat
                     unfold VarInstance_Ty, Var, ids, Ren_Ty, Ren1, ren1,
                      Up_Ty_Ty, Up_Ty, up_Ty, Subst_Ty, Subst1, subst1.

Tactic Notation "auto_unfold" "in" "*" := repeat
                                           unfold VarInstance_Ty, Var, ids,
                                            Ren_Ty, Ren1, ren1, Up_Ty_Ty,
                                            Up_Ty, up_Ty, Subst_Ty, Subst1,
                                            subst1 in *.

Ltac asimpl' := repeat (first
                 [ progress setoid_rewrite substSubst_Ty_pointwise
                 | progress setoid_rewrite substSubst_Ty
                 | progress setoid_rewrite substRen_Ty_pointwise
                 | progress setoid_rewrite substRen_Ty
                 | progress setoid_rewrite renSubst_Ty_pointwise
                 | progress setoid_rewrite renSubst_Ty
                 | progress setoid_rewrite renRen'_Ty_pointwise
                 | progress setoid_rewrite renRen_Ty
                 | progress setoid_rewrite varLRen'_Ty_pointwise
                 | progress setoid_rewrite varLRen'_Ty
                 | progress setoid_rewrite varL'_Ty_pointwise
                 | progress setoid_rewrite varL'_Ty
                 | progress setoid_rewrite rinstId'_Ty_pointwise
                 | progress setoid_rewrite rinstId'_Ty
                 | progress setoid_rewrite instId'_Ty_pointwise
                 | progress setoid_rewrite instId'_Ty
                 | progress
                    unfold up_list_Ty_Ty, up_Ty_Ty, upRen_list_Ty_Ty,
                     upRen_Ty_Ty, up_ren
                 | progress cbn[subst_Ty ren_Ty]
                 | progress fsimpl ]).

Ltac asimpl := check_no_evars;
                repeat
                 unfold VarInstance_Ty, Var, ids, Ren_Ty, Ren1, ren1,
                  Up_Ty_Ty, Up_Ty, up_Ty, Subst_Ty, Subst1, subst1 in *;
                asimpl'; minimize.

Tactic Notation "asimpl" "in" hyp(J) := revert J; asimpl; intros J.

Tactic Notation "auto_case" := auto_case ltac:(asimpl; cbn; eauto).

Ltac substify := auto_unfold; try setoid_rewrite rinstInst'_Ty_pointwise;
                  try setoid_rewrite rinstInst'_Ty.

Ltac renamify := auto_unfold; try setoid_rewrite_left rinstInst'_Ty_pointwise;
                  try setoid_rewrite_left rinstInst'_Ty.

End Core.

Module Extra.

Import
Core.

Arguments var_Ty {n_Ty}.

Arguments Mu {n_Ty}.

Arguments Arr {n_Ty}.

Arguments Sum {n_Ty}.

Arguments Prod {n_Ty}.

Arguments Nat {n_Ty}.

Arguments Void {n_Ty}.

#[global] Hint Opaque subst_Ty: rewrite.

#[global] Hint Opaque ren_Ty: rewrite.

End Extra.

Module interface.

Export Core.

Export Extra.

End interface.

Export interface.

