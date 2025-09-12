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
.

Module TypingNotations.
Export ScopedNotations.
Export SyntaxNotations.
Notation "Γ |- e ∈ τ" := (typing Γ e τ) (at level 70).
End TypingNotations.

Import TypingNotations.




