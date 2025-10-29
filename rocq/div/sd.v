Require Import div.eff.
Require Import div.div.

Import eff.Notations.

(** * Syntax directed version of the effect system *)

Module IN.

Inductive typing_val {n} (Γ : Ctx n) : Val n -> Ty 0 -> Prop := 
  | t_var x : 
    typing_val Γ (var x) (Γ x)

  | t_zero : 
    typing_val Γ zero Nat

  | t_succ k : 
    typing_val Γ k Nat ->
    typing_val Γ (succ k) Nat


  | t_prod v1 v2 τ1 τ2 ε : 
    typing_val Γ v1 τ1 ->
    typing_val Γ v2 τ2 -> 
    typing_val Γ (prod v1 v2) (Prod ε τ1 τ2)

  | t_inl v τ1 τ2 : 
    typing_val Γ v τ1 ->
    typing_val Γ (inj true v) (Sum τ1 τ2)

  | t_inr v τ1 τ2 : 
    typing_val Γ v τ2 ->
    typing_val Γ (inj false v) (Sum τ1 τ2)

  | t_abs e τ1 τ2 ε  : 
    typing (τ1 .: Γ) e τ2 ε -> 
    typing_val Γ (abs e) (Arr τ1 ε τ2)

  | t_rec v τ : 
    allows_rec_ty τ = true ->
    typing_val (τ .: Γ) v τ -> 
    typing_val Γ (rec v) τ

  | t_fold v τ : 
    typing_val Γ v (τ [(Mu τ) ..]) ->
    typing_val Γ (fold v) (Mu τ)

with typing {n} (Γ : Ctx n) : Tm n -> Ty 0 -> Eff -> Prop := 
  | t_ret v τ ε :
    typing_val Γ v τ ->
    typing Γ (ret v) τ ε

  | t_let e1 e2 τ1 τ2 ε1 ε2 ε :
    typing Γ e1 τ1 ε1 ->
    typing (τ1 .: Γ) e2 τ2 ε2 ->
    ε1 ⊕ ε2 <: ε ->
    typing Γ (let_ e1 e2) τ2 ε

  | t_app v1 v2 τ1 τ2 ε1 ε : 
    typing_val Γ v1 (Arr τ1 ε1 τ2) -> 
    typing_val Γ v2 τ1 -> 
    ε1 <: ε ->
    typing Γ (app v1 v2) τ2 ε

  | t_ifz v e0 e1 τ ε :
    typing_val Γ v Nat -> 
    typing Γ e0 τ ε -> 
    typing (Nat .: Γ) e1 τ ε -> 
    typing Γ (ifz v e0 e1) τ ε

  | t_prj1 v τ1 τ2 ε1 ε :
    typing_val Γ v (Prod ε1 τ1 τ2) -> 
    ε1 <: ε ->
    typing Γ (prj1 v) τ1 ε

  | t_prj2 v τ1 τ2 ε1 ε  :
    typing_val Γ v (Prod ε1 τ1 τ2) -> 
    ε1 <: ε ->    
    typing Γ (prj2 v) τ2 ε

  | t_case v e1 e2 τ1 τ2 τ ε : 
    typing_val Γ v (Sum τ1 τ2) ->
    typing (τ1 .: Γ) e1 τ ε ->
    typing (τ2 .: Γ) e2 τ ε ->
    typing Γ (case v e1 e2) τ ε

 | t_unfold v τ : 
    typing_val Γ v (Mu τ) ->
    typing Γ (unfold v) (τ [(Mu τ) ..]) ⊤
.

(* The t_sub rule of the previous system is *admissible*. We can 
   prove it as a lemma *)
Lemma t_sub {n : nat} (Γ : Ctx n) e τ ε1 ε2 :
   typing Γ e τ ε1 -> 
   ε1 <: ε2 -> 
   typing Γ e τ ε2.
Proof. 
  intro h. move: ε2. induction h.
  all: intros ε' LE.
  all: try solve [econstructor; eauto using eff.trans with rec].
  - destruct ε'; try done. econstructor. eauto. 
Qed.

End IN.



(* ----------------------------------------------------------- *)
(** * Proof of equivalence for the type-and-effect systems *)

Section IN_Equivalence.


Fixpoint IN_to_Eff {n : nat} (Γ : Ctx n) e τ ε1 :
  IN.typing Γ e τ ε1 -> div.typing Γ e τ ε1
with IN_to_Eff_val {n : nat} (Γ : Ctx n) v τ :
  IN.typing_val Γ v τ -> div.typing_val Γ v τ.
Proof. 
  all: intro h.
  all: inversion h; subst.
  all: try solve [econstructor; eauto].
  - eapply div.t_sub.
    econstructor; eauto. done.
  - eapply div.t_sub with (ε1 := ε0 ⊕ ε2); auto.
    econstructor; eauto.
  - eapply div.t_sub with (ε1 := ε0); eauto.
    econstructor; eauto.
  - eapply div.t_sub with (ε1 := ε0); eauto.
    econstructor; eauto.
  - eapply div.t_sub with (ε1 := ε0); eauto.
    econstructor; eauto.
Qed.

Fixpoint Eff_to_IN {n : nat} (Γ : Ctx n) e τ ε1 :
  div.typing Γ e τ ε1 -> IN.typing Γ e τ ε1
with Eff_to_IN_val {n : nat} (Γ : Ctx n) v τ :
  div.typing_val Γ v τ -> IN.typing_val Γ v τ.
Proof.
  all: intro h.
  all: inversion h; subst.
  all: try solve [econstructor; eauto using eff.refl, IN.t_sub].
  eapply IN.t_sub; eauto.
Qed.

End IN_Equivalence.



Module OUT.

Definition lub (e1 : Eff) (e2 : Eff) := 
  match e1 , e2 with 
  | Top , _ => Top
  | _ , Top => Top
  | Bot, Bot => Bot
  end.

(* LUB calculates a least upper bound. *)
Lemma lub_ub1 e1 e2 : e1 <: lub e1 e2.
Proof. destruct e1; destruct e2; cbn; done. Qed.
Lemma lub_ube e1 e2 : e2 <: lub e1 e2.
Proof. destruct e1; destruct e2; cbn; done. Qed.
Lemma lub_least e1 e2 e : e1 <: e -> e2 <: e -> lub e1 e2 <: e.
Proof. destruct e1; destruct e2; destruct e; done. Qed.


Inductive typing_val {n} (Γ : Ctx n) : Val n -> Ty 0 -> Prop := 
  | t_var x : 
    typing_val Γ (var x) (Γ x)

  | t_zero : 
    typing_val Γ zero Nat

  | t_succ k : 
    typing_val Γ k Nat ->
    typing_val Γ (succ k) Nat

  | t_pair v1 v2 τ1 τ2 ε : 
    typing_val Γ v1 τ1 ->
    typing_val Γ v2 τ2 -> 
    typing_val Γ (prod v1 v2) (Prod ε τ1 τ2)

  | t_inj1 v τ1 τ2 : 
    typing_val Γ v τ1 ->
    typing_val Γ (inj true v) (Sum τ1 τ2)

  | t_inj2 v τ1 τ2 : 
    typing_val Γ v τ2 ->
    typing_val Γ (inj false v) (Sum τ1 τ2)


  | t_rec v τ : 
    allows_rec_ty τ = true ->
    typing_val (τ .: Γ) v τ -> 
    typing_val Γ (rec v) τ

  | t_fold v τ : 
    typing_val Γ v (τ [(Mu τ) ..]) ->
    typing_val Γ (fold v) (Mu τ)


with typing {n} (Γ : Ctx n) : Tm n -> Ty 0 -> Eff -> Prop := 
  | t_ret v τ :
    typing_val Γ v τ ->
    typing Γ (ret v) τ ⊥

  | t_let e1 e2 τ1 τ2 ε1 ε2 :
    typing Γ e1 τ1 ε1 ->
    typing (τ1 .: Γ) e2 τ2 ε2 ->
    typing Γ (let_ e1 e2) τ2 (ε1 ⊕ ε2) 


 | t_unfold v τ : 
    typing_val Γ v (Mu τ) ->
    typing Γ (unfold v) (τ [(Mu τ) ..]) ⊤
.

Definition t_var' {n} (Γ : Ctx n) x τ   : Γ x = τ -> typing_val Γ (var x) τ.
intros <-. eapply t_var. Qed.

#[export] Hint Resolve t_var' : rec.

#[export] Hint Constructors typing_val typing : rec.

  
End OUT.

Module OUT_Equivalence.

Fixpoint OUT_to_Eff {n : nat} (Γ : Ctx n) e τ ε1 :
  OUT.typing Γ e τ ε1 -> div.typing Γ e τ ε1
with OUT_to_Eff_val {n : nat} (Γ : Ctx n) v τ :
  OUT.typing_val Γ v τ -> div.typing_val Γ v τ.
Proof. 
(* FILL IN HERE *) Admitted.

Fixpoint Eff_to_OUT {n : nat} (Γ : Ctx n) e τ ε1 :
  div.typing Γ e τ ε1 -> exists ε, OUT.typing Γ e τ ε /\ ε <: ε1
with Eff_to_OUT_val {n : nat} (Γ : Ctx n) v τ :
  div.typing_val Γ v τ -> OUT.typing_val Γ v τ.
Proof.
(* FILL IN HERE *) Admitted.

End OUT_Equivalence.



