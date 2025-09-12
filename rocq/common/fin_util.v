Require Export common.fintype.

Import ScopedNotations.

(* Convenient fin values for examples. *)
Module FinValues.
Definition f0 {n} : fin (S n) := var_zero.
Definition f1 {n} : fin (S (S n)) := Some f0.
Definition f2 {n} : fin (S (S (S n))) := Some f1.
Definition f3 {n} : fin (S (S (S (S n)))) := Some f2.
End FinValues.

(* Equality for fins is decidable *)
Definition fin_eqb {n} : fin n -> fin n -> bool.
Proof.
    induction n.
    - intros. contradiction.
    - intros i1 i2. destruct i1 as [i1' | ] eqn: H1, i2 as [i2' | ] eqn: H2.
        + (*i1 = Some i1', i2 = Some i2'*)
            destruct (IHn i1' i2') eqn: IHe.
            * (*i1' = i2'*) apply true.
            * (*i1' <> i2'*) apply false.
        + (*i1 = Some i1', i2 = None*) apply false.
        + (*i1 = None, i2 = Some i2'*) apply false.
        + (*i1 = None, i2 = None*) apply true.
Defined.

Lemma fin_eqb_eq : forall n (i1 i2 : fin n),
    fin_eqb i1 i2 = true <-> i1 = i2.
Proof.
    induction n.
    - intros. contradiction.
    - intros. split; intros H.
        + destruct i1 as [i1' | ], i2 as [i2' | ]; try inversion H; auto.
            f_equal. apply IHn. destruct (fin_eqb i1' i2') eqn: He; auto.
        + subst. destruct i2 as [i2' | ]; auto.
            specialize IHn with i2' i2' as [IHn1 IHn2].
            specialize IHn2 with (1 := eq_refl i2').
            simpl. rewrite IHn2. reflexivity.
Qed.

Lemma fin_eqb_neq : forall n (i1 i2 : fin n),
    fin_eqb i1 i2 = false <-> i1 <> i2.
Proof.
    intros. split; intros.
    - intros Heq. apply fin_eqb_eq in Heq. rewrite Heq in H. discriminate.
    - destruct (fin_eqb i1 i2) eqn: He; auto. rewrite fin_eqb_eq in He.
        contradiction.
Qed.


Lemma fin_eqb_true {n}{i:fin n}: fin_eqb i i = true.
  assert (EQ : i = i). auto.
  rewrite <- (fin_eqb_eq n i i) in EQ. auto.
Qed.


Definition ren_inj {n m} (renamer : ren n m) :=
    (forall i1 i2, renamer i1 = renamer i2 -> i1 = i2).

Definition ren_match {n m X} (renamer : ren n m)
    (fn : fin n -> X) (fm : fin m -> X) :=
    forall i, fn i = fm (renamer i).

Definition default_or_preimage {n m X} (id : X) (fm : fin m -> X) (renamer : ren n m) :=
    (forall j, fm j = id \/ exists i, j = renamer i).

Inductive ren_preimage_cases {n m} (renamer : ren n m) (j : fin m) : Type :=
    | preimage (i : fin n) (H : j = renamer i) : ren_preimage_cases renamer j
    | no_preimage (H : forall (i : fin n), renamer i <> j) : ren_preimage_cases renamer j
    .

Definition ren_preimage_dec {n m} :
    forall (renamer : ren n m) (j : fin m), ren_preimage_cases renamer j.
Proof.
    induction n; intros.
    - eapply no_preimage. intros. destruct i.
    - destruct (fin_eqb (renamer None) j) eqn: HNone.
        + apply preimage with (i := None). rewrite fin_eqb_eq in HNone. auto.
        + remember (fun jn => renamer (shift jn)) as renamer_n.
            destruct (IHn renamer_n j).
            * apply preimage with (i := shift i). subst. reflexivity.
            * apply no_preimage. intros. destruct i as [i' |].
                -- specialize H with i'. intros Hj; subst. contradiction.
                -- rewrite fin_eqb_neq in HNone. auto.
Qed.

Definition match_pre_id {n m X} (renamer : ren n m) (fn : fin n -> X)
    (default : X) : fin m -> X := fun j =>
    match ren_preimage_dec renamer j with
    | preimage _ _ i H => fn i
    | no_preimage _ _ H => default
    end.

Lemma match_pre_id_inj_sound :
    forall n m X (renamer : ren n m) (fn : fin n -> X) (default : X),
    ren_inj renamer ->
    ren_match renamer fn (match_pre_id renamer fn default) /\
    default_or_preimage default (match_pre_id renamer fn default) renamer.
Proof.
    intros. split.
    - unfold ren_match. intros. unfold match_pre_id.
        destruct (ren_preimage_dec renamer (renamer i)) eqn: Hc.
        + f_equal. apply H. assumption.
        + clear Hc. specialize H0 with i. contradiction.
    - unfold default_or_preimage. intros. unfold match_pre_id.
        destruct (ren_preimage_dec renamer j) eqn: Hc.
        + right. exists i. assumption.
        + left. reflexivity.
Qed.


Lemma ren_match_shift :
    forall n X (fn : fin n -> X) x_new,
    ren_match shift fn (x_new .: fn).
Proof.
    unfold ren_match. intros. auto.
Qed.

(*
Lemma ren_match_up_ren' :
    forall n X (fn : fin n -> X) x x_new,
    ren_match up_ren' (x .: fn) (x .: (x_new .: fn)).
Proof.
    unfold ren_match. intros.
    destruct i as [i' | ]; auto.
Qed.

Lemma ren_match_up2_ren' :
    forall n X (fn : fin n -> X) x1 x2 x_new,
    ren_match up2_ren'
        (x1 .: (x2 .: fn))
        (x1 .: (x2 .: (x_new .: fn))).
Proof.
    unfold ren_match. intros.
    destruct i as [[i'' |] | ]; auto.
Qed.
*)

(* instantiate an equality between equivalent functions. *)
Lemma x_equal
     : forall (A B : Type) (f g : A -> B) (x : A), f = g -> f x = g x.
Proof. intros. rewrite H. auto. Qed.


Definition env_map {n}{A B} (f : A -> B) (ρ : fin n -> A) : fin n -> B :=
  fun x => f (ρ (x)).


(* requires functional ext *)
(*
Lemma env_map_cons {n} {A B} (a : A) (b : fin n -> A) (f : A -> B) : 
  env_map f ( a .: b ) = f a .: env_map f b .
Proof.
  unfold env_map. fext. intro x.
  unfold scons. destruct x. auto. auto.
Qed.
*)

Lemma scons_inj1 {n A} (a c : A) (b d : fin n -> A) : ( a .: b ) = (c .: d) -> a = c.
Proof.
  intros h.
  pose (h1 := x_equal _ _ (a .: b) (c .: d) var_zero h).
  simpl in h1.
  auto.
Qed.

(*
Lemma scons_inj2 {n A} (a c : A) (b d : fin n -> A) : ( a .: b ) = (c .: d) -> b = d.
Proof.
  intros h.
  fext. intro x.
  pose (h1 := x_equal _ _ (a .: b) (c .: d) (shift x) h).
  simpl in h1.
  auto.
Qed.
*)
