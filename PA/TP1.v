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

Parameter EM : forall P, ~~ P -> P.



Lemma drinker : exists p:Person, ~ Mortal p -> forall q:Person, ~ (Mortal q).
Proof.
	apply EM.
	intro.
	apply H.
	exists Socrate.
	intros.
	intro.
	apply H.
	exists q.
	intros.
	contradiction.
Qed.

(* Element type *)
Parameter Elt:Type.
(* Binary operator *)
Parameter op : Elt -> Elt -> Elt.
(* Inversion operation *)
Parameter inv : Elt -> Elt.
(* Associativity of op*)
Parameter assoc : forall a b c, op (op a b) c = op a (op b c).
Parameter e:Elt.
(* there exists an identity element *)
Parameter id_l : forall a, op e a = a.
Parameter id_r : forall a, op a e = a.
(* there exists an inverse element *)
Parameter inv_l : forall a, op (inv a) a = e.
Parameter inv_r : forall a, op a (inv a) = e.

Lemma group : forall x y, inv (op x y) = op (inv y) (inv x).
Proof.
	intros.
	transitivity (op (op (inv y) (inv x)) (op (op x y) (inv (op x y)))).
	rewrite assoc.
	rewrite assoc.
	rewrite <- assoc with (a:=inv x) (b:=x).
	rewrite inv_l.
	rewrite id_l.
	rewrite <- assoc with (a:=inv y) (b:=y).
	rewrite inv_l.
	rewrite id_l.
	reflexivity.

	rewrite inv_r.
	rewrite id_r.
	reflexivity.
Qed.



