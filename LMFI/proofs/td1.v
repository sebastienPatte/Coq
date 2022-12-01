Section Ex1.
Variables A B C : Prop.

Lemma E1F1 : A -> A.
Proof.
	intro.
	exact H.
Qed. 

Lemma E1F2 : (A -> B) -> (B -> C) -> A -> C.
Proof.
	intros.
	apply H0.
	apply H.
	apply H1.
Qed.

Lemma E1F3 : A /\ B <-> B /\ A.
Proof.
	unfold "<->".
	split.
	all : intro; split; apply H.
Qed.

Lemma E1F4 : A \/ B <-> B \/ A.
Proof.
	unfold "<->".
	split.
	all: intro; destruct H.
	1,3: right; apply H.
	1,2: left; apply H.
	(* - right; apply H.
	- left ; apply H.
	- right; apply H.
	- left ; apply H. *)
Qed.


Lemma E1F5 : (A /\ B) /\ C <-> A /\ (B /\ C).
Proof.
	unfold "<->".
	split.
	all: intro; destruct H.
	- destruct H; split. 
		* apply H.
		* split. apply H1. apply H0.
	- destruct H0. split. split.
		* apply H.
		* apply H0.
		* apply H1.
Qed.
	 

Lemma E1F6 : (A \/ B) \/ C <-> A \/ (B \/ C).
Proof.
	unfold "<->".
	all: split; intros; destruct H.
	- destruct H. 
		* left; apply H.
		* right; left; apply H.
	- right; right; apply H. 
	- left; left; apply H.
	- destruct H. 
		* left; right; apply H.
		* right; apply H.
Qed.

Lemma E1F7 : A -> ~~A.
Proof.
	intro.
	unfold not.
	intros.
	apply H0.
	apply H.
Qed.

Lemma E1F8 : (A -> B) -> ~B -> ~A.
Proof.
	intro.
	unfold not.
	intros.
	apply H0.
	apply H.
	apply H1.
Qed.

Lemma E1F9 : ~~(A \/ ~A).
Proof.
	unfold "~".
	intro.
	apply H.
	right.
	intro.
	apply H.
	left.
	apply H0.
Qed.

End Ex1.

Section Ex2.

Variables X Y : Set.
Variables P Q : X -> Prop.
Variables R : X -> Y -> Prop.

Lemma E2F1 : (forall x, P x /\ Q x) <-> (forall x, P x) /\ (forall x, Q x).
Proof.
	unfold "<->".
	split.
	- intro. split; apply H.
	- intro. destruct H. split.
		* apply H. 
		* apply H0.
Qed.

Lemma E2F2 : (exists x, P x \/ Q x) <-> (exists x, P x) \/ (exists x, Q x).
Proof.
	unfold iff.
	split; intro.
	- destruct H. destruct H.
		* left. exists x. apply H.
		* right. exists x. apply H.
	- destruct H. destruct H. 
		* exists x. left. apply H.
		* destruct H. exists x. right. apply H.
Qed.    

Lemma E2F3 : (exists y, forall x, R x y) -> forall x, exists y, R x y.
Proof.
	intros.
	destruct H.
	exists x0.
	apply H.
Qed.


End Ex2.

Section Ex3.

Variables A B C : Prop.


Lemma imp_refl : A -> A.
Proof.
	intro.
	apply H.
Qed.

Lemma imp_trans : (A -> B) /\ (B -> C) -> (A -> C).
Proof.
	intros.
	destruct H.
	apply H1.
	apply H.
	apply H0.
Qed.

Lemma iso_curry : (A /\ B -> C) <-> (A->B->C).
Proof.
	unfold iff.
	split; intros; apply H.
	- split.
		* apply H0.
		* apply H1.
	- destruct H0. apply H0.
	- destruct H0. apply H1.
Qed.

Lemma distr_forall {T:Type}: forall x:T, (A /\ B) <-> (forall x:T, A) /\ (forall x:T, B).
	Proof.
		unfold iff.
		split; intro.
		-  split; destruct H; intro.
			* apply H.
			* apply H0.
		- split; destruct H.
			*  apply (H x).
			* apply (H0 x).
Qed.

Lemma distr_exist {T:Type}: (exists x:T, (A \/ B)) <-> (exists x:T, A) \/ (exists x:T, B).
Proof.
	unfold iff. 
	split; intro; destruct H. 
	- destruct H. 
		* left. exists x. apply H.
		* right. exists x. apply H.

	-  destruct H. exists x. left. apply H.
	-  destruct H. exists x. right. apply H.
Qed.


End Ex3.

Section Ex4.
Variables A B C : Prop.
Axiom not_not_elim : forall A : Prop, ~~A -> A.

Lemma doubleNeg : A <-> ~ ~A.
Proof.
	unfold iff.
	split; intro.
	unfold "~".
	intros.
	apply H0.
	apply H.
	apply not_not_elim .
	apply H.
Qed.

Lemma tier_exclu : A \/ ~ A.
Proof.
	apply not_not_elim.
	apply E1F9.
Qed.

Lemma morgan_forall {T:Type} (P: T -> Prop): ~ (forall x:T, P x) <-> exists x:T, (~(P x)).
Proof.
	
	unfold iff.
	split.
	
	- apply not_not_elim.  

End Ex4.

