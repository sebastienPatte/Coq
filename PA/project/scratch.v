Require Import Ltac.
 
Ltac tauto1 := match goal with
	| |- True => idtac "trivial"; trivial
	|_:?A |- ?A => idtac "assumption"; assumption 
	|_:False |- _ => idtac "contradiction"; contradiction

	| |- (?A -> ?B) => idtac "imp_I"; intro; tauto1
	|H:(?A -> ?B) |- ?C  => 
		let H1 := fresh in
		idtac "imp_E";
		cut A;
		[ intro H1; apply H in H1 | ];
		clear H; tauto1 

	|H: ?A /\ ?B |- _  => idtac "and_E"; destruct H; tauto1
	| |-  ?A /\ ?B  => idtac "and_I"; split; tauto1

	| |- ?A \/ ?B  => idtac "or_I1"; left; tauto1
	| |- ?A \/ ?B  => idtac "or_I2"; right; tauto1
	| H: ?A \/ ?B |- _  => idtac "or_E"; destruct H; tauto1
	


	end.


Parameter A B C:Prop.

Lemma t7 : (A -> C) -> (B -> C) -> A \/ B -> C. 
Proof.
	tauto1.
Qed.

Lemma t : False -> A.
Proof. tauto1. Qed.

Lemma t2 : A /\ B -> A.
Proof. tauto1. Qed.

Lemma t3 : A /\ B -> B.
Proof. tauto1. Qed.

Lemma t4 : A /\ B -> B /\ A.
Proof. tauto1. Qed.

Lemma t5 : A -> A \/ B.
Proof. tauto1. Qed.

Lemma t6 : B -> B \/ A. 
Proof. tauto1. Qed.



Lemma t8 : A -> (A -> B) -> B. 
Proof. tauto1. Qed.

Lemma t9 : A -> (A -> B) -> (B -> C) -> B. 
Proof. tauto1. Qed.

Lemma t10 : A -> (A -> B) -> (B -> C) -> C. 
Proof. tauto1. Qed.
