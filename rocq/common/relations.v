

(* Reflexive, transitive closure of a relation. *)
Inductive multi {A} (step : A -> A -> Prop)  : A -> A -> Prop := 
  | ms_refl e : 
    multi step e e 
  | ms_trans e1 e2 e3 :
    step e1 e2 -> multi step e2 e3 ->
    multi step e1 e3.
Arguments ms_refl {_}{_}{_}.
Arguments ms_trans {_}{_}{_}{_}{_}.

Lemma ms_refl' {A} (step : A -> A -> Prop) e1 e2 : 
  e1 = e2 -> multi step e1 e2.
Proof.  intro. subst. eapply ms_refl. Qed.

Lemma ms_one {A} (step : A -> A -> Prop) e1 e2 :
  step e1 e2 -> multi step e1 e2.
Proof. intros. eapply ms_trans; eauto. eapply ms_refl. Qed.

(* Append two reduction sequences *)
Lemma ms_app {A} {R : A -> A -> Prop} {e1 e2 e3 } : 
  multi R e1 e2 -> multi R e2 e3 -> multi R e1 e3. 
Proof.
  induction 1.
  subst; auto.
  intro h.
  eapply ms_trans. eauto. 
  eapply IHmulti. auto.
Qed.


(* Iterate a step relation *exactly* n-times *)
Inductive step_n {A} (step : A -> A -> Prop) : nat -> A -> A -> Prop := 
  | s_done e : 
    step_n step 0 e e
  | s_next k e1 e2 e3 : 
    step e1 e2 -> 
    step_n step k e2 e3 -> 
    step_n step (S k) e1 e3.

Arguments s_done {_}{_}{_}.
Arguments s_next {_}{_}{_}{_}{_}.


Lemma s_done' {A} (step : A -> A -> Prop) e1 e2 : 
  e1 = e2 -> step_n step 0 e1 e2.
Proof.  intro. subst. eapply s_done. Qed.

Lemma s_one' {A} (step : A -> A -> Prop) e1 e2 :
  step e1 e2 -> step_n step 1 e1 e2.
Proof. intros. eapply s_next; eauto. eapply s_done. Qed.

Lemma s_app {A} (step : A -> A -> Prop) k1 k2 e1 e2 e3 :
  step_n step k1 e1 e2 -> step_n step k2 e2 e3 -> 
  step_n step (k1 + k2) e1 e3.
Proof.
  intros h1 h2.
  induction h1; cbn; eauto.
  eapply s_next; eauto.
Qed.

Lemma step_n_multi {A} (step : A -> A -> Prop) n e1 e2 :
  step_n step n e1 e2 -> multi step e1 e2.
Proof.
  induction 1; econstructor; eauto.
Qed.

Lemma multi_step_n {A} (step : A -> A -> Prop) e1 e2 :
  multi step e1 e2 -> exists n, step_n step n e1 e2.
Proof.
  induction 1. eexists; econstructor; eauto.
  destruct IHmulti. eexists; econstructor; eauto.
Qed.
