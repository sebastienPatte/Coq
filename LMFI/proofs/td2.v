Lemma add_0_l : forall n, 0 + n = n.
Proof.
	simpl.
	reflexivity.
Qed.

Lemma add_succ_l : forall n m, S n + m = S (n + m).
Proof.
	simpl.
	reflexivity.
Qed.

Print Nat.add.

Lemma add_0_r : forall n, n + 0 = n.
Proof.
	intro.
	induction n.
	- simpl; reflexivity.
	- simpl; rewrite IHn; reflexivity.
Qed.
	
Lemma add_succ_r : forall n m, n + S m = S (n + m).
Proof.
	
	induction n; simpl.
	- reflexivity.
	- intros. rewrite IHn. reflexivity.
Qed.  

Lemma add_assoc : forall n m p, (n + m) + p = n + (m + p).
Proof.
	induction n; simpl.
	- reflexivity.
	- intros. rewrite IHn. reflexivity.
Qed.


Lemma add_comm : forall n m, n + m = m + n.
Proof.
	induction n.
	- simpl. symmetry. apply add_0_r.
	- simpl.  symmetry. rewrite IHn. apply add_succ_r.
Qed.


Lemma mul_0_l : forall n, 0 * n = 0.
Proof.
simpl. reflexivity.
Qed.

Lemma mul_succ_l : forall n m, S n * m = m + n * m.
Proof.
simpl. reflexivity.
Qed.

Lemma mul_0_r : forall n, n * 0 = 0.
Proof.
	induction n; simpl.
	- reflexivity.
	- apply IHn.
Qed.



Lemma mul_succ_r : forall n m, n * S m = n + n * m.
Proof.
	induction n; simpl.
	- reflexivity.
	- intros. f_equal. rewrite IHn. rewrite <- add_assoc. rewrite <- add_assoc. f_equal. apply add_comm.
Qed.


Lemma mul_distr : forall n m p, (n + m) * p = n * p + m * p.
Proof.
	induction n; simpl.
	- reflexivity.
	- intros. rewrite add_assoc. rewrite IHn. reflexivity. 
Qed.

Lemma mul_assoc : forall n m p, (n * m) * p = n * (m * p).
Proof.
	induction n; simpl.
	- reflexivity.
	- intros. rewrite mul_distr. rewrite IHn. reflexivity.     
Qed.

Lemma mul_comm : forall n m, n * m = m * n.
Proof.
	induction n; simpl; intro.
	- rewrite mul_0_r. reflexivity.
	- rewrite mul_succ_r. rewrite IHn. reflexivity.  
Qed.

Definition le (n m : nat) := exists p, n + p = m.
Infix "<=" := le .

Lemma le_refl : forall n, n <= n.
Proof.
	intros. exists 0.
	apply add_0_r.
Qed.

Lemma le_trans : forall n m p, n <= m -> m <= p -> n <= p.
Proof.
	unfold le. intros.
	destruct H. destruct H0.
	exists (x+x0). 
	rewrite <- H0.
	rewrite <- H.
	rewrite add_assoc.
	reflexivity.
Qed.

Lemma le_antisym : forall n m, n <= m -> m <= n -> n = m.
Proof.
	unfold le. 
	intros.
	destruct H,H0.
	rewrite <- H in H0.
	rewrite add_assoc in H0.
	assert (x+x0 = 0).
	
	
	rewrite <- H0.
	rewrite <- H.
	exists 0.
Qed.


