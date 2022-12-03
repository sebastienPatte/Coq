Require Import List.
Require Import Lia.
Import ListNotations.

Lemma nil_conc {A:Type} (l: list A) : nil ++ l = l.
Proof.
	unfold "++".
	reflexivity.
Qed.

Lemma conc_nil {A:Type} (l: list A) : l ++ nil = l.
Proof.
	induction l.
	- unfold "++". reflexivity.
	- simpl. rewrite IHl. reflexivity.  
Qed.

Print length.

Fixpoint length  {A:Type} (l:list A):  nat := 
	match l with  
	|[] => 0
	|_::ll => S(length ll)
end.

Lemma length_conc {A:Type} (l1 l2:list A) : length (l1 ++ l2) = length l1 + length l2.
Proof.
	induction l1; simpl.
	- reflexivity.
	- f_equal. apply IHl1.
Qed.

Fixpoint rev {A:Type} (l:list A): list A := 
	match l with 
	|[] => []
	|h::t => (rev t)++[h]
end.

Lemma rev_length {A:Type} (l:list A) : length (rev l) = length l.
Proof.
	induction l.
	- simpl. reflexivity.
	- simpl. rewrite length_conc. simpl. rewrite IHl. lia.
Qed.
	

Lemma rev_conc {A:Type} (l1 l2:list A) : rev (l1++l2) = (rev l2) ++ (rev l1).
Proof.
	induction l1; simpl.
	- rewrite conc_nil. reflexivity.
	- rewrite IHl1.  rewrite app_assoc. reflexivity.
Qed.

Fixpoint split {A} (l:list A) :=
 match l with
 | [] => ([],[])
 | a::l => let (l1,l2) := split l in (a::l2,l1)
 end.

Fixpoint splitbis {A} (l:list A) :=
 match l with
 | [] => ([],[])
 | [a] => ([a],[])
 | a::b::l => let (l1,l2) := splitbis l in (a::l1,b::l2)
 end.

Lemma split_equiv_aux {A} (l:list A) :
  split l = splitbis l /\ forall x, split (x::l) = splitbis (x::l).
Proof.
induction l.
	- simpl. split; reflexivity.  
	- split.  
		* apply IHl.
		* intro. 
			simpl. destruct IHl. 
			rewrite H. destruct (splitbis l).
			reflexivity.
Qed.


Lemma split_contains {A} (l:list A) :
 let (l1,l2) := split l in
 forall x, In x l <-> In x l1 \/ In x l2.
Proof.
  induction l.
  - intros x. unfold iff. split. 
    * auto.
    * intro. destruct H; apply H.
  - simpl. destruct (split l).
    simpl. intro. rewrite IHl. intuition.
Qed.


Lemma split_length {A} (l:list A) :
 let (l1,l2) := split l in
 length l1 = length l2 \/ length l1 = S (length l2).
  Proof.
  induction l.
  - simpl. left. reflexivity.
  - simpl. destruct (split l).
    destruct IHl.
    * right. simpl. rewrite H. reflexivity.
    * left. simpl. rewrite H. reflexivity.
Qed.   



  