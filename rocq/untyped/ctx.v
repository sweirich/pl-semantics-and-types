(** This file defines Pitt's definition of Contextual Approximation
    as the largest compatible, adequate, preorder 
    for scoped relations.  
*)

Require Export untyped.stack.

Import Lists.List.ListNotations.
Import SyntaxNotations.
Import stack.Notations.

Open Scope list_scope.
Open Scope rec_scope.

(* --------------------------------------------------------- *)

(** A scoped relation is a binary relation between two objects
    in the same scope. We make this generic so that we can use 
    the same definition for terms and values. *)
Definition scoped_relation (T : nat -> Type) : Type := forall n, T n -> T n -> Prop.

(** A scoped relation is a pre-order if it is reflexive and transitive. 
    We define type classes for these concepts, similar to the 
    type classes found in Rocq's standard library.
    For more background on typeclasses, see this chapter 
    https://softwarefoundations.cis.upenn.edu/qc-current/Typeclasses.html
 *)
Class ScopedReflexive {T : nat -> Type} (R : scoped_relation T) : Prop := 
  scoped_refl : forall n x, R n x x.
Class ScopedTransitive {T : nat -> Type} (R : scoped_relation T) : Prop := 
  scoped_trans : forall n (t1 t2 t3 : T n), R _ t1 t2 -> R _ t2 t3 -> R _ t1 t3.

Arguments scoped_refl {_}{_}.
Arguments scoped_trans {_}{_}{_}{_}.

Class ScopedPreOrder {T : nat -> Type} (R : scoped_relation T) := 
  { po_scoped_refl  :: ScopedReflexive R ;
    po_scoped_trans :: ScopedTransitive R
  }.

(** A relation is Adequate when related *closed* values 
    obey approximation. *)
Class Adequate (RE : scoped_relation Tm) := 
  adequate : forall (e e' : Tm 0), RE _ e e' -> (nil, e) ⊑ (nil, e').

(** Compatibility is specific to the syntax of the language. It states
    that the relation is preserved through all syntactic forms. Because 
    our language has two mutual types (Tm and Val) we need to index 
    compatibility by two relations, that must work together. *)
Class Compatible (RE : scoped_relation Tm) (RV : scoped_relation Val) := 
  { val_var n x :
      RV n (var x) (var x) ;

    val_unit n : 
      RV n unit unit ;

    val_zero n : 
      RV n zero zero ;

    val_succ n x y :
      RV n x y ->
      RV n (succ x) (succ y) ;


    val_abs n e1 e2 : 
      RE _ e1 e2 -> 
      RV n (abs e1) (abs e2) ;

    comp_ret n v1 v2 : 
      RV _ v1 v2 ->
      RE n (ret v1) (ret v2) ;

    comp_let n e1 e2 e1' e2' : 
      RE _ e1 e2 -> 
      RE _ e1' e2' ->
      RE n (let_ e1 e1') (let_ e2 e2') ;

    comp_ifz n v1 v2 e1 e2 e1' e2' : 
      RV _ v1 v2 -> 
      RE _ e1 e2 -> 
      RE _ e1' e2' -> 
      RE n (ifz v1 e1 e1') (ifz v2 e2 e2') ;


    comp_app n v1 v2 v1' v2' :
      RV _ v1 v2 -> 
      RV _ v1' v2' -> 
      RE n (app v1 v1') (app v2 v2') ;


}.



(** ---------------------------------------------------- * *)

(* Any relation that is compatible is also reflexive. We prove this 
   by (mutual) induction on the syntax of Tm and Val. *)

(** Combined mutual induction scheme *)
Scheme Val_Tm_rec := Induction for Val Sort Prop 
    with 
    Tm_Val_rec := Induction for Tm Sort Prop.

Combined Scheme Val_Tm_mutrec from 
  Tm_Val_rec, Val_Tm_rec.

Lemma Compatible_refl RE RV : 
  Compatible RE RV -> 
  forall n, (forall e, RE n e e) /\ (forall v, RV n v v).
Proof. 
  intros CC.
  eapply Val_Tm_mutrec with 
    (P0 := fun n t => RE n t t)
    (P := fun n v => RV n v v).
  all: intros.
  - eapply val_var.
  - eapply val_unit.
  - eapply val_abs; eauto.
  - eapply val_zero.
  - eapply val_succ; eauto.
(* FILL IN HERE *) Admitted.

Instance Compatible_ReflexiveRE {RE}{RV} `{H : Compatible RE RV} : ScopedReflexive RE.
Proof.
  intro n.
  move: (Compatible_refl _ _ H) => h1.
  eapply (h1 n).
Qed.

Instance Compatible_ReflexiveRV {RE RV} `{H : Compatible RE RV} : ScopedReflexive RV.
Proof.
  intro n.
  move: (Compatible_refl _ _ H) => h1.
  eapply (h1 n).
Qed.

(** ---------------------------------------------------- * *)

(** * CTX: Pitt's contextual preorder *)

(** Pitt's defines contextual approximation as the largest 
    Compatible, Adequate, PreOrder. We can model that definition 
    by saying that any two terms are related by CTX when they 
    are related by any Compatible, Adequate, Transitive relation 
    (We showed above that Compatible implies reflexive so we 
    don't need to include that in the definition.)
    Note that RV is unconstrained --- it only needs to be 
    compatible with RE.
*)
Inductive CTX n (e e' : Tm n) : Prop := 
  rel : forall RE RV 
      `{Compatible RE RV} 
      `{Adequate RE} 
      `{ScopedTransitive _ RE},
      RE n e e' -> CTX n e e'.



(* This definition shows that CTX is at least as big as any Compatible,
   Adequate, Transitive relation, but it doesn't show that it has any of these
   properties itself. We need to prove it.

   It is difficult to show that CTX is compatible, but we will show that
   it is both Adequate (easy) and Transitive (a little more difficult). *)

(** Adequacy of CTX is straightforward *)

Instance Adequate_CTX : Adequate CTX.
Proof.
  unfold Adequate.
  intros e e' h1 h.
  inversion h1. eapply adequate; eauto.
Qed.

(** * Transtivity of CTX *)

(* We can show that CTX is transitive by showing that the transitive 
   closure of two Adequate, Transitive, Compatible relations is 
   itself Adequate, Transitive and Compatible. *)

(** transitive closure of RE1 + RE2 *) 
Inductive OR_star {T : nat -> Type} (RE1 RE2: scoped_relation T) n (t1 t2 : T n) : Prop := 
  | OR_1 : 
    RE1 n t1 t2 -> OR_star RE1 RE2 n t1 t2 
  | OR_2 : 
    RE2 n t1 t2 -> OR_star RE1 RE2 n t1 t2 
  | OR_trans t3 : 
    OR_star RE1 RE2 n t1 t3
    -> OR_star RE1 RE2 n t3 t2 
    -> OR_star RE1 RE2 n t1 t2. 

Instance Reflexive_OR_star {T} {RE1 RE2 : scoped_relation T} 
  `{ScopedReflexive _ RE1} : ScopedReflexive (OR_star RE1 RE2).
Proof.
- intros n t.
  eapply OR_1; eapply scoped_refl; eauto.
Qed.

Instance Transitive_OR_star {T} {RE1 RE2 : scoped_relation T} :
  ScopedTransitive (OR_star RE1 RE2).
Proof.
- intros n t1 t2 t3 O1 O2.
  eapply OR_trans; eauto.
Qed.

Instance PreOrder_OR_star {T} {RE1 RE2 : scoped_relation T} 
  `{ScopedReflexive T RE1} : 
  ScopedPreOrder (OR_star RE1 RE2).
Proof.
  split; typeclasses eauto.
Qed.

Instance Adequate_OR_star {RE1 RE2 : scoped_relation Tm} `{Adequate RE1} `{Adequate RE2} : Adequate (OR_star RE1 RE2). 
Proof.
unfold Adequate in *.
intros e e' O. induction O; eauto. transitivity ([] : stack, t3); auto.
Qed.

(* Tactic to help with compatiblility proof below. *)
Ltac compat_case t1 t2 f := 
match goal with [ H1 : OR_star _ _ _ t1 t2 |- _ ] => 
                  induction H1; [ 
                    eapply OR_1; eapply f; eauto |
                    eapply OR_2; eapply f; eauto |
                    eapply OR_trans; eauto] end;
try match goal with [ |- _ _ ?t ?t ] => 
  eapply scoped_refl; eauto using Compatible_ReflexiveRV, Compatible_ReflexiveRE end;
eauto.

Instance Compatible_OR_star 
  {RE1 RE2 : scoped_relation Tm}
  {RV1 RV2 : scoped_relation Val} 
   `{ScopedPreOrder Tm RE1} `{ScopedPreOrder Tm RE2}
   `{Compatible RE1 RV1} `{Compatible RE2 RV2} : 
  Compatible (OR_star RE1 RE2) (OR_star RV1 RV2).      
Proof.               
constructor.
all: intros.
- eapply OR_1; eapply val_var; eauto.
- eapply OR_1; eapply val_unit; eauto.
- eapply OR_1; eapply val_zero; eauto.
- compat_case x y @val_succ.
(* FILL IN HERE *) Admitted.

Instance Transitive_CTX : ScopedTransitive CTX.
Proof.
  intros n t1 t2 t3 C1 C2.
  destruct C1 as [RE1 RV1 ? ? ? R1].
  destruct C2 as [RE2 RV2 ? ? ? R2].
  eapply (rel n t1 t3 (OR_star RE1 RE2) (OR_star RV1 RV2)).
  eapply OR_trans. eapply OR_1; eauto. eapply OR_2; eauto.
  Unshelve.
  + eapply Compatible_OR_star; eauto.
    Unshelve. split; typeclasses eauto. 
    split; typeclasses eauto.
Qed.

