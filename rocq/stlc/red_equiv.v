(* Show that small-step and big-step are equivalent. *)
Require Import stlc.red.
Require Import stlc.typing.
Require Import stlc.small_step.

Import TypingNotations.
Import RedNotations.

(** Our goal for this section is to prove that if e ~>* v then e ⇓ v.
To do so, we need to look at each big step rule and derive a corresponding 
small step rule of the semantics. *)

Module BigSmall.

(* Big.s_val
     : forall v : Tm 0, is_value v = true -> v ⇓ v *)

Lemma s_val : forall v, is_value v = true -> v ⟱ v.
Proof.
  intros v h.
  split; eauto. 
  eapply ms_refl; eauto.
Qed.

(* Big.s_app
     : forall (e1 : Tm 0) (e1' : Tm 1) (e2 v1 v2 : Tm 0), 
       e1 ⇓ abs e1' -> e2 ⇓ v1 -> e1'[v1..] ⇓ v2 -> app e1 e2 ⇓ v2 *)

Lemma s_app : 
  forall (e1 : Tm 0) (e1' : Tm 1) (e2 v1 v2 : Tm 0), 
      e1 ⟱ abs e1' -> e2 ⟱ v1 -> e1'[v1 ..] ⟱ v2 -> app e1 e2 ⟱ v2.
Proof.
  intros e1 e1' e2 v1 v2 [h1 _] [h2 Vv1] [h3 Vv2].
  split; auto.
  eapply @ms_app with (e2 := app (abs e1') e2).
  { eapply ms_app_cong1; eauto. }
  eapply @ms_app with (e2 := app (abs e1') v1).
  { eapply ms_app_cong2; eauto. }
  eapply ms_trans. eapply Small.s_beta. auto. auto.
Qed.

Lemma same_semantics : 
  (forall e v, e ⇓ v  -> e ⟱ v).
Proof.
  intros e v h. induction h.
  all: intros.
  - eapply s_val; auto.
  - eapply s_app; eauto.
Qed.
    
End BigSmall.

Module SmallBig.

Lemma same_semantics_step : 
  (forall e e', (e ⤳ e') -> forall v, e' ⇓ v -> e ⇓ v).
Proof.
  intros e e' h1.
  induction h1.
  all: intros w h2.
  - eapply Big.s_app. eapply Big.s_val; auto.
       eapply Big.s_val; eauto.
       eauto.
  - inversion h2; try done. subst. clear h2.
    eapply Big.s_app; eauto.
  - inversion h2; try done. subst. clear h2.
    eapply Big.s_app; eauto.
    Qed.

(* This is by induction on the bigstep relation.
 *)
Lemma same_semantics_step' : 
  (forall e' v, e' ⇓ v -> forall e, (e ⤳ e') -> e ⇓ v).
Proof.
  intros e' v h. induction h. 
  - intros e hS. 
    (* Case s_val : v ⇓ v *)
    inversion hS; subst.
    (* rule out those that don't produce a value *)
    all: try solve [simpl in H; done].
    + destruct e0; cbn in H; try done.
      ++ destruct f. done. asimpl.
         eapply Big.s_app; eauto.
         eapply Big.s_val; eauto.
         eapply Big.s_val; eauto.
         asimpl. 
         eapply Big.s_val; eauto.
      ++ asimpl.
         eapply Big.s_app; eauto.
         eapply Big.s_val; eauto.
         eapply Big.s_val; eauto.
         asimpl. 
         eapply Big.s_val.
         cbn. done.
      ++ asimpl.
         eapply Big.s_app; eauto.
         eapply Big.s_val; eauto.
         eapply Big.s_val; eauto.
         asimpl. 
         eapply Big.s_val.
         cbn. done.
      - (* Case s_app: e ⤳ e1 e2  and e1 e2 ⇓ v2 *)
    intros e hS.
    inversion hS; subst.
    + destruct e0; asimpl in H1; try done.
      ++ destruct f. done. asimpl in H. subst.
         cbn in H1. done.
      ++ inversion H. subst.
         eapply Big.s_app.
         eapply Big.s_val; eauto.
         eapply Big.s_val; eauto.
         asimpl.
         eapply Big.s_app; eauto.
    + eapply Big.s_app; eauto.
    + eapply Big.s_app; eauto.
    Qed.

Lemma same_semantics : forall e v,  e ⟱ v -> e ⇓ v.
Proof.
  intros e v [h V].
  induction h.
  - eapply Big.s_val; auto.
  - eapply same_semantics_step; eauto.
Qed.

End SmallBig.


 
