(* Lemma cons_inj  : 
forall x1 x2 :Type, forall l1 l2 : list Type,
 cons x1 l1 = cons x2 l2 -> x1=x2 /\ l1=l2.
Proof.
	intros.
	injection H.
	split.
	apply H1.
	apply H0.
Qed. *)

Parameter A:Type.

Definition tl (l: list A) : list A :=
	match l with 
	nil => nil
	|cons _ t => t
	end
.

Definition hd (v:A) (l: list A) : A :=
	match l with 
	nil =>  v
	|cons h t => h
	end
.

Lemma cons_inj  : 
forall x1 x2 :A, forall l1 l2 : list A,
 cons x1 l1 = cons x2 l2 -> x1=x2 /\ l1=l2.
Proof.
	intros.
	split.
	apply f_equal with (f:= hd x1) in H.
	
	simpl in H.
	apply H.
	apply f_equal with (f:= tl) in H.
	simpl in H.
	apply H.
Qed.

Definition Nil (l: list A) := 
	match l with 
	nil => True
	|_ => False
	end
.


Lemma cons_discr : 
forall x : A, forall l : list A, nil <> cons x l.
Proof.
	intros.
	
	unfold not.
	intro.
	apply f_equal with (f:=Nil) in H.
	unfold Nil in H.
	rewrite <-  H.
	exact I.
	
