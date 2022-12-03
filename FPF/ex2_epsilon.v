Require Import ssreflect.
Require Import Classical_Pred_Type.

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


Eval cbv in (dec( forall (P:nat->Prop), forall x, P x)).

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
  case (H (eps P)); intro H1.
  left.
  exists (eps P).
  assumption.
  right.
  intro H2.
  apply H1.
  destruct H2 as [x HP].
  apply (eps_p P x).
  assumption.
Qed.


Lemma eps_all (P:nat->Prop) :
  (forall i, dec (P i))->
  dec (forall x, P x).
Proof.
intro.
  apply eps_ex in H as H'.

  unfold dec.
  unfold dec in H,H'.
  case H'.
  intros.
  
  right.
  unfold not.
  intros.
  specialize (H x) as HP.
  right.
  unfold not.
  intros.

  specialize (H0 x) as H0.
  destruct (H') as [H3| H4].
Admitted.

  

(* The drinker's paradox : in classical logic,
   in every bar, there is a person such that, if this person drinks,
   everybody drinks *)


(* epsilon allows us to prove a weaker version *)
Lemma Drink_weak : forall  (P:nat->Prop),
    exists n, ~P n -> forall m, ~P m.
Proof. 
  intros.
  exists (eps P).
  intros.
  intros H1.
  apply eps_p in H1.
  contradiction.
Qed.


(* or the regular version, if the predicate is decidable *)
Lemma Drink :  forall  (P:nat->Prop),
    (forall i, dec (P i)) ->
    exists n, P n -> forall m, P m.
Proof.
  intros.
  
  apply eps_all in H as H'.
  unfold dec in H'.
  case H'.
  intros.
  exists 0.
  intro.
  apply H0.
  intros.
  
  apply not_all_ex_not in H0.
  destruct H0.
  exists x.
  intro.
  contradiction.
Qed.