Require Import Classical.

Check classic.

Definition cont A := A -> False.
Definition throw {A} (k : cont A) (v : A) : False := k v.

Definition callcc {A : Prop} : ((cont A) -> A) -> A
 := 
  fun f => 
    match @classic A with
    | or_introl a => a
    | or_intror na => f na 
    end.











(* ------------------------------------------------- *)

(*
Inductive and (A B : Prop) : Prop := 
    conj : A -> B -> A /\ B.
Inductive or (A B : Prop) : Prop :=  
    or_introl : A -> A \/ B 
  | or_intror : B -> A \/ B.
Definition not = 
  fun A : Prop => A -> False.
*)


Parameter P Q : Prop.

Definition demorgan1 : not P /\ not Q -> not (P \/ Q) := 
  fun npnq => match npnq with 
             | conj np nq => 
                fun p_or_q => 
                  match p_or_q with 
                  | or_introl p => np p
                  | or_intror q => nq q
                  end
             end.

Lemma demorgan2 : not (P \/ Q) -> not P /\ not Q.
intros h. split. intros p. apply h. left. exact p.
intros q. apply h. right. exact q.
Defined.

Lemma demorgan3 : not P \/ not Q -> not (P /\ Q).
intro h. destruct h. intros pq. destruct pq. 
apply H. exact H0.
intros pq. destruct pq. apply H. exact H1.
Defined.

Check @classic.
Check @callcc.

Lemma demorgan4 : not (P /\ Q) -> not P \/ not Q.
intros npq. eapply callcc.
intro k.
left. intro p. eapply (throw k).
right. intro q. apply npq. split. exact p. 
exact q.
Defined.

Definition decide {A} : A \/ cont A :=
  callcc (fun k => or_intror (fun a => 
             throw k (or_introl a))).






















