From Stdlib Require Import Psatz.
From Stdlib Require Import Arith.

Require Export common.core.
Require Export untyped.stack.

Import Lists.List.ListNotations.
Import SyntaxNotations.
Import stack.Notations.

Open Scope list_scope.
Open Scope rec_scope.


(* --------------------------------------------------------- *)

Definition scoped_relation (T : nat -> Type) := forall n, T n -> T n -> Prop.

Class Reflexive {T : nat -> Type} (R : scoped_relation T) : Prop := 
  { scoped_refl : forall n x, R n x x }.

Class Transitive {T : nat -> Type} (R : scoped_relation T) : Prop := 
  { scoped_trans : forall n (t1 t2 t3 : T n), R _ t1 t2 -> R _ t2 t3 -> R _ t1 t3 }.

Class PreOrder {T : nat -> Type} (R : scoped_relation T) := 
  { po_scoped_refl  : Reflexive R ;
    po_scoped_trans : Transitive R
  }.

Definition Adequate (RE : scoped_relation Tm) := 
  forall (e e' : Tm 0), RE _ e e' -> Small.halts (nil, e) -> Small.halts (nil, e').

Existing Class Adequate.

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

(** * Contextual preorder definition *)

Inductive CTX n (e e' : Tm n) : Prop := 
  rel : forall RE RV, 
      Compatible RE RV -> 
      Adequate RE -> 
      Transitive RE ->
      RE n e e' -> CTX n e e'.

(** * We want to know properties about CTX *)


(** ---------------------------------------------------- * *)

(* Any relation that is compatible is also reflexive *)

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

Instance Compatible_ReflexiveRE {RE}{RV} `{H : Compatible RE RV} : Reflexive RE.
constructor. intro n.
move: (Compatible_refl _ _ H) => h1.
eapply (h1 n).
Qed.

Instance Compatible_ReflexiveRV {RE RV} `{H : Compatible RE RV} : Reflexive RV.
constructor. intro n.
move: (Compatible_refl _ _ H) => h1.
eapply (h1 n).
Qed.


(* ------------------------------------------------------------------ *)

(* We won't show that CTX is compatible here, but we can show that it 
   is both Adequate and Transitive *)

(** Adequacy of CTX is straightforward *)

Instance Adequate_CTX : Adequate CTX.
unfold Adequate.
intros e e' h1 h.
inversion h1.
eapply H0; eauto.
Qed.

(* ------------------------------------------------------------------ *)

(** Transtivity of CTX is more difficult to show *)

Inductive OR_star {T : nat -> Type} (RE1 RE2: scoped_relation T) n (t1 t2 : T n) : Prop := 
  | OR_1 : RE1 n t1 t2 -> OR_star RE1 RE2 n t1 t2 
  | OR_2 : RE2 n t1 t2 -> OR_star RE1 RE2 n t1 t2 
  | OR_trans t3 : 
    OR_star RE1 RE2 n t1 t3
    -> OR_star RE1 RE2 n t3 t2 
    -> OR_star RE1 RE2 n t1 t2. 

Instance Reflexive_OR_star {T} {RE1 RE2 : scoped_relation T} 
  `{Reflexive T RE1} : Reflexive (OR_star RE1 RE2).
Proof.
constructor.
- intros n t.
  eapply OR_1; eapply scoped_refl; eauto.
Qed.

Instance Transitive_OR_star {T} {RE1 RE2 : scoped_relation T} :
  Transitive (OR_star RE1 RE2).
Proof.
constructor.
- intros n t1 t2 t3 O1 O2.    
  eapply OR_trans; eauto.
Qed.

Instance PreOrder_OR_star {T} {RE1 RE2 : scoped_relation T} 
  `{Reflexive T RE1} : 
  PreOrder (OR_star RE1 RE2).
split. constructor; eapply scoped_refl. constructor; eapply scoped_trans.
Qed.

Instance Adequate_OR_star {RE1 RE2 : scoped_relation Tm} `{Adequate RE1} `{Adequate RE2} : Adequate (OR_star RE1 RE2). 
Proof.
unfold Adequate in *.
intros e e' O. induction O; eauto.
Qed.

Ltac compat_case H1 f := 
induction H1; [ 
  eapply OR_1; eapply f; eauto |
  eapply OR_2; eapply f; eauto |
  eapply OR_trans; eauto].


Instance Compatible_OR_star 
  {RE1 RE2 : scoped_relation Tm}
  {RV1 RV2 : scoped_relation Val} 
   `{PreOrder Tm RE1} `{PreOrder Tm RE2}
   `{Reflexive _ RV1} `{Reflexive _ RV2}
   `{Compatible RE1 RV1} `{Compatible RE2 RV2} : 
  Compatible (OR_star RE1 RE2) (OR_star RV1 RV2).      
Proof.               
constructor.
all: intros.
- eapply OR_1; eapply val_var; eauto.
- eapply OR_1; eapply val_unit; eauto.
- eapply OR_1; eapply val_zero; eauto.
- compat_case H5 @val_succ.
(* FILL IN HERE *) Admitted.

Instance Transitive_CTX : Transitive CTX.
constructor.
- intros n t1 t2 t3 C1 C2.
  destruct C1 as [RE1 RV1 ? ? ? R1].
  destruct C2 as [RE2 RV2 ? ? ? R2].
  eapply (rel n t1 t3 (OR_star RE1 RE2) (OR_star RV1 RV2)).
  + eapply Compatible_OR_star; eauto.
    Unshelve. split; eauto. 
    constructor. eapply scoped_refl. 
    split; eauto.
    constructor. eapply scoped_refl.
  + eapply Adequate_OR_star; eauto.
  + eapply PreOrder_OR_star; eauto.
  + eapply OR_trans. eapply OR_1; eauto.
    eapply OR_2; eauto.
Qed.

(** --------------------------------------------------------- *)

