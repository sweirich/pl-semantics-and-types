From Stdlib Require Export ssreflect.
From Stdlib Require Export Program.Equality.
Require Export common.core.
Require Export common.fintype.

Require Export common.fin_util.
Require Export common.relations.
Require Export common.renaming.

Import ScopedNotations.

Inductive Ty : Type := 
  | Nat : Ty
  | Arr : Ty -> Ty -> Ty
  | Box : Ty -> Ty.

Definition Ctx (n : nat) := fin n -> Ty.

Inductive Val {n} (Γ : Ctx n) : Ty -> Type := 
  | var x : 
    Val Γ (Γ x)

  | zero : 
    Val Γ Nat 

  | succ : 
    Val Γ Nat -> Val Γ Nat

  | abs τ1 τ2 : 
    Tm (τ1 .: Γ) τ2 ->
    Val Γ (Arr τ1 τ2)

  | fun_ τ1 τ2  : 
    Tm (τ1 .: (Arr τ1 (Box τ2) .: Γ)) (Box τ2)  -> 
    Val Γ (Arr τ1 (Box τ2))

  | box τ : 
    Val Γ τ -> 
    Val Γ (Box τ)

with Tm {n} (Γ : Ctx n) : Ty  -> Type := 
  | ret τ :
    Val Γ τ ->
    Tm Γ τ 

  | let_ τ1 τ2 : 
    Tm Γ τ1 ->
    Tm (τ1 .: Γ) τ2 ->
    Tm Γ τ2

  | unbox τ1 τ2  :
    Tm Γ (Box τ1)  ->
    Tm (τ1 .: Γ) (Box τ2) ->
    Tm Γ (Box τ2)

  | app τ1 τ2  : 
    Val Γ (Arr τ1 τ2) -> 
    Val Γ τ1 -> 
    Tm Γ τ2 

  | ifz τ : 
    Val Γ Nat -> Tm Γ τ -> Tm (Nat .: Γ) τ -> Tm Γ τ
.

(*
Definition sub {n}{m}(Γ: Ctx m)(Δ: Ctx n) : 
Definition subst {n} {Γ : Ctx n} : sub Δ Γ -> Tm Γ τ -> Tm Δ τ.

Inductive step {τ} : Tm null τ -> Tm null τ -> Prop :=.
*)

Arguments ret{_}{_}{_}.
Arguments let_{_}{_}{_}{_}.
Arguments unbox{_}{_}{_}{_}.
Arguments app{_}{_}{_}{_}.
Arguments ifz {_}{_}{_}.

Arguments var{_}{_}.
Arguments zero{_}{_}.
Arguments succ{_}{_}.
Arguments abs{_}{_}{_}{_}.
Arguments fun_{_}{_}{_}{_}.
Arguments box{_}{_}{_}.

(*
CoInductive Delay (A : Type) : Type := 
  | Now : A -> Delay A
  | Later : Delay A -> Delay A
.

Definition Delay_loop' {B} : 
  (Delay B -> Delay B) -> Delay B.
cofix loop.
eapply (fun f => f (loop (fun x => Later _ (f x)))).
Defined.

Definition Delay_loop {A B} : 
  ((A -> Delay B) -> (A -> Delay B)) -> 
  (A -> Delay B).
*)

Definition Timed (A : Type) : Type :=  nat -> option A.

Definition pure {A} (v:A) : Timed A := fun (x:nat) => Some v.

Definition bind {A B} (t : Timed A) (u : A -> Timed B) : Timed B := 
  fun x => match t x with
        | Some y => u y x
        | None => None
        end.

Fixpoint loop {A B} 
  (f: (A -> Timed B) -> (A -> Timed B)) : A -> Timed B := 
  fun a x =>
  match x with 
  | O => None
  | S n => f (fun b y => loop f b n) a (S n)
  end. 

Definition plus : nat -> nat -> Timed nat := 
  fun x => loop (fun (plus' : nat -> Timed nat) => 
        fun y => match y with 
              | 0 => pure x
              | S z => bind (plus' z) (fun w => pure (S w))
              end).

Eval cbv in (plus 5 2 10).

Module Denotational.


Fixpoint denot_Ty (τ : Ty) : Type := 
  match τ with 
  | Nat => nat
  | Arr τ1 τ2 => denot_Ty τ1 -> denot_Ty τ2 
  | Box τ => Timed (denot_Ty τ)
  end.

Definition Env {n} (Γ : Ctx n) := forall (x :fin n), denot_Ty (Γ x).

Definition empty_Env : Env null := fun x => match x with end.

Definition cons_Env {n} {τ} {Γ : Ctx n} (D : denot_Ty τ) (ρ :Env Γ) :  Env (τ .: Γ).
unfold Env in *. intro x. destruct x; cbn. eauto. auto. Defined.

Fixpoint denot {n}{Γ : Ctx n}{τ} 
    (e : Tm Γ τ) :Env Γ -> denot_Ty τ 
with 
denot_val {n}{Γ : Ctx n}{τ} 
    (v : Val Γ τ) : Env Γ -> denot_Ty τ.
Proof.
- dependent destruction e.
all: intros X.
+ exact
  (denot_val _ _ _ v X). 
+ (* let case *)
  move: (denot _ Γ τ1 e1 X) => d1.
  eapply (denot _ (τ1 .: Γ) τ2 e2 (cons_Env d1 X)).
+ (* unbox case, must use bind *)
  move: (denot _ _ _ e1 X) => d1. 
  eapply bind. eapply d1. intro x.
  eapply (denot _ _ _ e2).
  eapply cons_Env; eauto. 
+ (* application case *)
  refine ((denot_val _ _ _ v X) 
          (denot_val _ _ _ v0 X)).
+ destruct (denot_val _ _ _ v X).
  * exact (denot _ _ _ e1 X).
  * exact (denot _ _ _ e2 (@cons_Env _ Nat _ d X)).
- destruct v eqn:hv.
  all: intros X.
  + (* var case *)
    eapply X.
  + (* zero case *)
    exact 0.
  + exact (S (denot_val _ _ _ v0 X)).
  + (* abs case *)
    exact (fun x => denot _ _ _ t (cons_Env x X)).
  + (* rec fun *)
    exact (loop (fun p x => denot _ _ _ t
             (cons_Env x (@cons_Env _ (Arr τ1 (Box τ2)) _ p X)))).
  + (* box case *)
    exact (pure (denot_val _ _ _ v0 X)).
Defined.


(*
Lemma compositionality : 
  (σ : sub Δ Γ)
  X = denot_sub σ
  denot e (σ X) = denot (e σ) X.


Lemma compositionality : 
  denot e (cons_Env (denot_val v X) X) = denot (e [v..]) X.

Lemma soundness τ : forall (e1 e2 : Tm null τ), 
    step e1 e2 -> denot e1 empty_Env = denot e2 empty_Env.
Abort.
*)

Import FinValues.

Example lit3 {n}{Γ : Ctx n} : Val Γ Nat := 
  (succ (succ (succ zero))).

Eval cbv in (denot_val lit3  empty_Env).


Example id3 : Tm null Nat := 
  (app (abs (ret (var f0))) lit3).

Eval cbn in (denot id3 empty_Env).


(* let f = ret (fun f x . ret (box x)) in 
   y <- f 3 ;; ret (box y) *)

Example triv : Tm null (Box Nat) := 
  let_ (ret (fun_ (ret (box (var f0))))) 
    (unbox (app (var f0) lit3) (ret (box (var f0)))).

Eval cbv in (denot triv empty_Env 1).

(* \x. ret (fun f y . case y of { 0 => ret (box x); S z => w <- f s ; ret (box (succ w)) *)
Example plus : Val null (Arr Nat (Arr Nat (Box Nat))) := 
  abs (ret (@fun_ _ (Nat .: null) Nat Nat
         (ifz (var f0)
            (ret (box (var f2)))
            (unbox 
               (@app _ 
                  (* z     y      f                      x *)
                  (Nat .: (Nat .: (Arr Nat (Box Nat) .: (Nat .: null)))) _ _
                      (var f2) (var f0))
               (ret (box (succ (var f0)))))))).

Eval cbv in (denot_val plus empty_Env 20).

Eval cbv in (denot (app plus lit3) empty_Env 20).

Definition e := (let_ (app plus lit3) (app (var f0) lit3)).

Check e.

Eval cbv in (denot e empty_Env 20).


Example loop {n}{Γ : Ctx n} {τ} : Val Γ (Arr Nat (Box τ)) := 
  fun_ (app (var f1) (var f0)).

Example omega {n}{Γ : Ctx n}  : Tm Γ (Box Nat) := 
  app loop zero.

Eval cbv in (denot omega empty_Env 20000).

Definition g : Tm null _ := (let_ omega (ret lit3)).

Check g. 

Eval cbv in (denot (let_ omega (ret lit3)) empty_Env).

Eval cbv in (denot (unbox omega (ret (box lit3))) empty_Env 1000).

End Denotational.
