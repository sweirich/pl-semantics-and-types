From Stdlib Require Export ssreflect.
From Stdlib Require Export Program.Equality.
Require Export common.fintype.
Require Export common.core.

Require Export stlc.syntax.

Import ScopedNotations.

Module SyntaxNotations.
Notation "⇑ σ" := (var var_zero .: σ >> ren_Tm ↑) (at level 70) : subst_scope.
End SyntaxNotations.

Import SyntaxNotations.

Definition Ctx (n : nat) := fin n -> Ty.

Inductive typing {n} (Γ : Ctx n) : Tm n -> Ty -> Prop := 
  | t_var x : 
    typing Γ (var x) (Γ x)

  | t_abs e τ1 τ2 : 
    typing (τ1 .: Γ) e τ2 -> 
    typing Γ (abs e) (Arr τ1 τ2)

  | t_app e1 e2 τ1 τ2 : 
    typing Γ e1 (Arr τ1 τ2) -> 
    typing Γ e2 τ1 -> 
    typing Γ (app e1 e2) τ2

  | t_lit k : 
    typing Γ (lit k) Nat
  | t_succ e :
    typing Γ e Nat -> 
    typing Γ (succ e) Nat

  | t_nrec e e0 e1 τ :
    typing Γ e Nat -> 
    typing Γ e0 τ -> 
    typing (Nat .: Γ) e1 (Arr τ τ) -> 
    typing Γ (nrec e e0 e1) τ

  | t_let e1 e2 τ1 τ2 :
    typing Γ e1 τ1 ->
    typing (τ1 .: Γ) e2 τ2 ->
    typing Γ (let_ e1 e2) τ2
.

Module TypingNotations.
Export ScopedNotations.
Export SyntaxNotations.
Notation "Γ |- e ∈ τ" := (typing Γ e τ) (at level 70).
End TypingNotations.

Import TypingNotations.




