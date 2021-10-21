Require Import ssreflect.
Definition dec (P:Prop) := P \/ ~P.

Lemma or_dec A B : (dec A) -> (dec B) -> dec (A \/ B).
Proof.
  unfold dec.  
  intros.
  destruct H.
  left.
  left.
  apply H.
  destruct H0.
  left.
  right.
  apply H0.
  right.
  unfold not.
  intros.
  destruct H1.
  contradiction.
  contradiction.
Qed.

(* We assume the existence of the epsilon operator *)                                             
Parameter eps : (nat -> Prop) -> nat.

Parameter eps_p : forall (P:nat->Prop) n, P n -> P (eps P).

(* Show that the quantifiers now preserve decidability *)
Lemma eps_ex (P:nat->Prop) :
  (forall i, dec (P i))->
   dec (exists x, P x).
Proof.
  unfold dec.  
  intros.
  specialize (H ).
  destruct H.
  left.
  exists 42.
  apply H.
  right.
  
  unfold not.
  
  intro.
  

Lemma eps_all (P:nat->Prop) :
  (forall i, dec (P i))->
  dec (forall x, P x).
Admitted.



(* The drinker's paradox : in classical logic,
   in every bar, there is a person such that, if this person drinks,
   everybody drinks *)


(* epsilon allows us to prove a weaker version *)
Lemma Drink_weak : forall  (P:nat->Prop),
    exists n, ~P n -> forall m, ~P m.
Admitted.

(* or the regular version, if the predicate is decidable *)
Lemma Drink :  forall  (P:nat->Prop),
    (forall i, dec (P i)) ->
    exists n, P n -> forall m, P m.
Admitted.
