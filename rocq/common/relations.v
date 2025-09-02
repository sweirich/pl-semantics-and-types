

(* Reflexive, transitive closure of a relation. *)
Inductive multi {A} (step : A -> A -> Prop)  : A -> A -> Prop := 
  | ms_refl e : 
    multi step e e 
  | ms_trans e1 e2 e3 :
    step e1 e2 -> multi step e2 e3 ->
    multi step e1 e3.
Arguments ms_refl {_}{_}{_}.
Arguments ms_trans {_}{_}{_}{_}{_}.

(* Append two reduction sequences *)
Lemma ms_app {A} {R : A -> A -> Prop} {e1 e2 e3 } : 
  multi R e1 e2 -> multi R e2 e3 -> multi R e1 e3. 
Proof.
  induction 1.
  auto.
  intro h.
  eapply ms_trans. eauto. 
  eapply IHmulti. auto.
Qed.


Inductive step_n {A} (step : A -> A -> Prop) : nat -> A -> A -> Prop := 
  | s_done e : 
    step_n step 0 e e
  | s_next k e1 e2 e3 : 
    step e1 e2 -> 
    step_n step k e2 e3 -> 
    step_n step (S k) e1 e3.
