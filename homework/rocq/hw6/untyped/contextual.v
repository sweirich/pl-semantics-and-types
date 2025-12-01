(** This module defines a "Contextual" preorder using arbitrary program 
    contexts (i.e. terms/values with a hole that can be filled in by open 
    terms. 

    It also shows that this relation is the same as CTX. i.e. 

            Contextual e e' <-> CTX e e'
    
    For the forward direction, we need to show that Contextual is 
    Adequate, Transitive and Compatible.

    For the backward direction, we need to show that for an arbitrary 
    C we have: 
            C{|e|} halts implies C{|e'|} halts

    we can use the adequacy of CTX to show this as long as we can show
    that plugging preserves CTX

          e <=CTX e' implies  C{|e|} <=CTX C{|e'|}

    For this we use the fact that CTX is compatible and that plugging 
    preserves compatible relations.

*)

Require Export untyped.equiv.

Import SyntaxNotations.
Import stack.Notations.

Open Scope list_scope.
Open Scope rec_scope.

(** The usual definition of contextual equivalence talks about 
    evaluating terms in arbitrary program contexts.

    i.e.  e <=C e' when  
          forall C,  halts C{|e|} implies halts C{|e'|} 

    This does in what step what CIU equivalence does in two: provides 
    definitions of free variables in e and e' and make observations.

    The notation C{|e|} takes a context C and term e and produces a term.
    The notation |- C : n asserts that if e : Tm n, then C{|e|} is closed.

    Note: we can't just think about plugging terms in contexts to produce 
    terms. Sometimes we may need to plug a term into a value to produce a 
    valu. Furthermore, we also want to talk about equality between values 
    in arbitrary term contexts, so that we can prove that this preorder is 
    Compatible.

    i.e.  v <=C v' when  forall C, halts C{|v|} implies halts C{|v'|} 

    This means that we need to plug values in contexts that produce terms 
    and values into contexts that produce values.
*)


(** * Context  *)

Variant ContextType : Type := TmCtx | ValCtx.
Definition CT (T : ContextType) : nat -> Type := 
  match T with | TmCtx => Tm | ValCtx => Val end.

(* A context has two natural number indices. The first is the scope of the
  hole, the second is the scope of the plugged term or value. (See definition
  of plug below.)

  A context also has two 'ContextType' indices. The first is the type of the
  hole. Do we plug terms or values in to this Context. The second describes
  whether this Context produces a term or value. For the second, we could
  split the Context type in to TmContext and ValContext. However, when we talk
  about composing contexts it is useful to be able to abstract over this
  index.  
*)
Inductive Context (m : nat) : nat -> ContextType -> ContextType -> Type :=
  | c_hole {T}    : Context m m T T
  | c_app1 {n T}  : Context m n T ValCtx -> Val n -> Context m n T TmCtx
  | c_app2 {n T}  : Val n -> Context m n T ValCtx -> Context m n T TmCtx
  | c_let1 {n T}  : Context m n T TmCtx -> Tm (S n) -> Context m n T TmCtx
  | c_let2 {n T}  : Tm n -> Context m (S n) T TmCtx -> Context m n T TmCtx
  | c_ifz1 {n T}  : Context m n T ValCtx -> Tm n -> Tm (S n) -> Context m n T TmCtx
  | c_ifz2 {n T}  : Val n -> Context m n T TmCtx -> Tm (S n) -> Context m n T TmCtx
  | c_ifz3 {n T}  : Val n -> Tm n -> Context m (S n) T TmCtx -> Context m n T TmCtx
  | c_ret  {n T}  : Context m n T ValCtx -> Context m n T TmCtx
  | v_abs {n T}   : Context m (S (S n)) T TmCtx -> Context m n T ValCtx
  | v_succ {n T}  : Context m n T ValCtx -> Context m n T ValCtx

.

Arguments c_hole {_}{_}.
Arguments c_app1 {_}{_}{_}.
Arguments c_app2 {_}{_}{_}.
Arguments c_let1 {_}{_}{_}.
Arguments c_let2 {_}{_}{_}.
Arguments c_ifz1 {_}{_}{_}.
Arguments c_ifz2 {_}{_}{_}.
Arguments c_ifz3 {_}{_}{_}.
Arguments c_ret {_}{_}{_}.
Arguments v_abs {_}{_}{_}.
Arguments v_succ {_}{_}{_}.


Local Notation "#" := c_hole (at level 7).

(* Do this in interactive mode to make working with the dependent types
   easier. But don't automate too much to make sure that we get the 
   arguments in the right order in app/case/prod *)
Fixpoint plug {m}{n}{T1 T2 : ContextType} (C : Context m n T1 T2) : CT T1 m -> CT T2 n.
destruct C.
all: intros e.
- eapply e.
- eapply (app (plug _ _ _ _ C e) v). 
- eapply (app v (plug _ _ _ _ C e)).
- eapply (let_ (plug _ _ _ _ C e) t).
- eapply (let_ t (plug _ _ _ _ C e)).
- eapply (ifz (plug _ _ _ _ C e) t t0).
- eapply (ifz v (plug _ _ _ _ C e) t).
- eapply (ifz v t (plug _ _ _ _ C e)).
- eapply (ret (plug _ _ _ _ C e)).
- eapply (abs (plug _ _ _ _ C e)).
- eapply (succ (plug _ _ _ _ C e)).

Defined.

Notation "C {| e |} " := (plug C e). 

Fixpoint compose {m n p}{T1 T2 T3} (C1 : Context m n T1 T2) (C2 : Context n p T2 T3) : Context m p T1 T3.
- dependent destruction C2.
  + exact C1.
  + eapply c_app1; eauto.
  + eapply c_app2; eauto.
  + eapply c_let1; eauto.
  + eapply c_let2; eauto.
  + eapply c_ifz1; eauto.
  + eapply c_ifz2; eauto.
  + eapply c_ifz3; eauto.
  + eapply c_ret; eauto.
  + eapply v_abs; eauto.
  + eapply v_succ; eauto.

Defined.

Infix "∘" := compose (at level 70).

Fixpoint compose_plug  {m n p T1 T2 T3} (C1 : Context m n T1 T2) (C2 : Context n p T2 T3) e : 
  C2 {| C1 {| e |} |} = (C1 ∘ C2) {| e |}.
Proof.
  dependent destruction C2.
  all: cbn.
  all: try (rewrite compose_plug; done).
  done.
Qed.

Definition Contextual (n : nat) (e1 : Tm n) (e2 : Tm n) :=
  forall (C :Context n 0 TmCtx TmCtx), Small.halts (nil, C {|e1|}) -> Small.halts (nil, C{|e2|}).
Definition ContextualVal (n : nat) (v1 : Val n) (v2 : Val n) := 
  forall (C :Context n 0 ValCtx TmCtx), Small.halts (nil, C {|v1|} ) -> Small.halts (nil, C {|v2|}).

Instance Adequate_Contextual : Adequate Contextual.
Proof.
  unfold Adequate.
  intros e e' C.
  unfold Contextual in C.
  specialize (C #).
  cbn in C.
  asimpl in C.
  done.
Qed.


Ltac compose_rewrite C1 := 
  repeat rewrite <- compose_plug in C1; cbn in C1; asimpl in C1; auto.

Instance Compatible_Contextual : Compatible Contextual ContextualVal.
split.
all: intros n.
all: repeat unfold Contextual, ContextualVal.
- intros x C. intro h. done.
- intros C. done.
- intros C. done.
- (* succ *)
  intros v1 v2 C1 C h.
  specialize (@C1 (v_succ # ∘ C)).
  compose_rewrite C1.

- (* abs *)
  intros e1 e2 C1 C h.
  specialize (@C1 (v_abs # ∘ C)).
  compose_rewrite C1.

- (* ret *)
  intros v1 v2 C1 C h.
  specialize (@C1 (c_ret # ∘ C)).
  compose_rewrite C1.
- (* let *) 
  intros e1 e2 e1' e2' C1 C2 C h.
  specialize (@C2 (c_let2 e2 # ∘ C)).
  compose_rewrite C2.
  specialize (@C1 (c_let1 # e1' ∘ C)).
  compose_rewrite C1.
- (* ifz *)
  intros v1 v2 e1 e2 e1' e2' C1 C2 C3 C h.
  specialize (@C3 (c_ifz3 v1 e1 # ∘ C)).
  compose_rewrite C3.
  specialize (@C2 (c_ifz2 v1 # e2' ∘ C)).
  compose_rewrite C2.
  specialize (@C1 (c_ifz1 # e2 e2' ∘ C)).
  compose_rewrite C1.

- (* app *)
  intros v1 v2 v1' v2' C1 C2 C h.
  specialize (@C2 (c_app2 v2 # ∘ C)).
  compose_rewrite C2.
  specialize (@C1 (c_app1 # v1' ∘ C)).
  compose_rewrite C1.

Qed.

Lemma Transitive_Contextual : ScopedTransitive Contextual.
Proof.
  intros n e1 e2 e3 CT1 CT2 C h.
  unfold Contextual in CT1, CT2.
  eauto.
Qed.

Lemma Contextual_CTX n e1 e2 : 
  Contextual n e1 e2 -> CTX n e1 e2.
Proof.
  intro h. 
  exists Contextual ContextualVal; eauto.
  eapply Compatible_Contextual.
  eapply Adequate_Contextual.
  eapply Transitive_Contextual.
Qed.

Fixpoint Compatible_plug n (e1 e2 : Tm n) 
  (RE : scoped_relation Tm)
  (RV : scoped_relation Val)
  (H : Compatible RE RV) :
  RE n e1 e2 -> forall m (C : Context n m TmCtx TmCtx),
  RE m C {|e1|} C {|e2|} 
with 
  Compatible_vplug n (e1 e2 : Tm n) 
  (RE : scoped_relation Tm)
  (RV : scoped_relation Val)
  (H : Compatible RE RV) :
  RE n e1 e2 -> forall m (C: Context n m TmCtx ValCtx),
  RV m (C {|e1|}) (C{|e2|}).
Proof.
- intros h m C.
  dependent destruction C.
  all: cbn.
  all: specialize (Compatible_plug n e1 e2 RE RV H h).
  all: specialize (Compatible_vplug n e1 e2 RE RV H h).
  + auto.
  + eapply comp_app. eapply Compatible_vplug; eauto.
    eapply scoped_refl. typeclasses eauto.
  + eapply comp_app. eapply scoped_refl. typeclasses eauto.
    eapply Compatible_vplug; eauto.
  + eapply comp_let. eapply Compatible_plug; eauto.
    eapply scoped_refl. typeclasses eauto.
  + eapply comp_let. 
    eapply scoped_refl. typeclasses eauto.
    eapply Compatible_plug.
  + eapply comp_ifz.
    eapply Compatible_vplug.
    eapply scoped_refl. typeclasses eauto.
    eapply scoped_refl. typeclasses eauto.
  + eapply comp_ifz.
    eapply scoped_refl. typeclasses eauto.
    eapply Compatible_plug.
    eapply scoped_refl. typeclasses eauto.
  + eapply comp_ifz.
    eapply scoped_refl. typeclasses eauto.
    eapply scoped_refl. typeclasses eauto.
    eapply Compatible_plug.
  + eapply comp_ret. 
    eapply Compatible_vplug.

- intros h m C.
  dependent destruction C.
  all: cbn.
  all: specialize (Compatible_plug n e1 e2 RE RV H h).
  all: specialize (Compatible_vplug n e1 e2 RE RV H h).
  + eapply val_abs. eauto.
  + eapply val_succ. eauto.

Qed.


Lemma CTX_Contextual n e1 e2 : 
  CTX n e1 e2 -> Contextual n e1 e2.
Proof.
  intro h. 
  unfold Contextual.
  intros C.
  eapply Adequate_CTX.
  eapply Compatible_plug; eauto.
  eapply Compatible_CTX.
Qed.



