Parameter A B C : Prop.
Lemma AimpA : A -> A.
Proof.
	intro.
	apply H.
Qed.


Lemma imp_trans : (A->B)->(B->C)->A->C.
Proof.
	intros.
	apply H in H1.
	apply H0 in H1.
	apply H1.
Qed.


Lemma and_comm : A /\ B -> B /\ A.
Proof.
	intro.
	destruct H .
	split.
	apply H0.
	apply H.
Qed.


Lemma or_comm : A \/ B -> B \/ A.
Proof.
	intro.
	destruct H.
	right.
	apply H.
	left.
	apply H.
Qed.


(* Using the Print command, print the proofs obtained 
for AimpA and imp_trans. What are these terms ? Does it help
understanding why -> is used both for logical implication 
and arrow types ? *)
Print AimpA.
Print imp_trans.

Lemma AimpNotA : A -> ~~A.
Proof.
	intro.
	unfold not.
	intros.
	apply H0 in H.
	apply H.
Qed.

Lemma noname : (A \/ B)/\ C -> A /\ C \/ B /\ C.
Proof.
	intro.
	destruct H.
	destruct H.
	left.
	split.
	apply H.
	apply H0.
	right.
	split.
	apply H.
	apply H0.
Qed.

Lemma EMequiv : (forall P:Prop, P \/ ~P) <-> (forall P:Prop, ~~P -> P).
Proof.
	unfold iff.
	split.
	intros.
	destruct H with P.
	apply H1.
	unfold not in H1.
	unfold not in H0.
	apply H0 in H1.
	contradiction.

	intros.
	apply H.
	unfold not.
	intros.
	apply H0.
	right.
	intro.
	apply H0.
	left.
	apply H1.
Qed.
	
	

(*Require Import Classical.*)

(* Socrate is a men, all mens are mortal, therefore socrate is mortal *)

Parameter Person:Type.
Parameter Socrate : Person.
Parameter Men Mortal : Person->Prop.

Lemma socrateMortal : Men Socrate /\ (forall P:Person, Men P -> Mortal P) -> Mortal Socrate.
Proof.
	intros.
	destruct H.
	apply H0 in H.
	apply H.
Qed.

(* Drinker's paradox *)



