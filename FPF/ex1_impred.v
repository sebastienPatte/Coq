Definition Leibniz (T:Type)(x : T) :=
  fun y=>
    forall P : T->Prop, (P y) -> (P x).

Lemma Lte : forall T x y, Leibniz T x y -> x = y.
Proof.
  unfold Leibniz.
  intros T x y P.
  apply (P (fun z => z=y)).
  reflexivity.
Qed.

Lemma etL : forall T x y, x = y -> Leibniz T x y.
Proof.
  unfold Leibniz.
  intros T x y P.
  rewrite P.
  intro.
  intro.
  apply H.
Qed.

  (* Do the following ones without using the two previous lemmas *)

Lemma L_sym : forall T x y, Leibniz T x y -> Leibniz T y x.
Proof.
  unfold Leibniz.
  intros T x y P P0.
  apply P.
  intro.
  apply H.
Qed.


Lemma L_trans : forall T x y z,
     Leibniz  T x y -> Leibniz T y z ->  Leibniz T x z.
Proof.
  unfold Leibniz. 
  intros T x y z.
  intros H H0 P.
  apply H.
  apply H0.
Qed.
  
  (* Redefine conjunction and/or disjunction and do the same *)
Definition imp_and (A:Prop)(B:Prop) := 
		forall X : Prop,  (A -> B -> X ) -> X.


(* We redefine less-or-equal *)

Inductive leq (n : nat) : nat -> Prop :=
|  leq_n : leq n n
|  leq_S : forall m, leq n m -> leq n (S m).

Lemma leq_trans : forall n m p, leq n m -> leq m p -> leq n p.
Proof.
intros n m p.
  (* here you have to chose between induction 1 and induction 2 *)
  intros.
  induction H0.
  apply H.
  apply leq_S.
  apply IHleq.
Qed.  
  (* Well-foundedness - here impredicative version *)
  
Definition Acc (T:Type)(R : T->T->Prop) :=
  fun x => forall P : T->Prop,
             (forall z, (forall y, R z y -> P y) -> P z) -> P x.

Lemma contra : forall  (P Q : Prop), P -> Q = ~(P) \/ Q.  
Proof.
Admitted.


Lemma eqnwf : forall n, ~(Acc nat eq n).
Proof.
  
  unfold Acc.
  intros n H.
  specialize (H (fun x => False)).
  simpl in H.
  apply H.
  intros.
  apply (H0 z).
  reflexivity.
Qed.
  
  
  
  

  
