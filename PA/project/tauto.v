Require Import Ltac Bool  List Nat Arith Lia.
Import ListNotations.

Parameter (A B C: Prop).

Lemma  impE: (A -> B) -> C.
Proof.
	intro.
	cut A.
	intro. 
	apply H in H0.
	clear H.
Abort.

Ltac tauto1_ d := match goal with
	|  		    |- True       => idtac d ": trivial" ; trivial
	| _:?A 	  |- ?A 	       => idtac d ": assumption" ; assumption 
	| _:False |- _ 	 	   => idtac d ": contradiction" ; contradiction
	|  		    |- (?A -> ?B) => idtac d " : imp_I" ; intro; tauto1_ (S(d))

	|H:(?A -> ?B) |- ?C  => 
		idtac d " : imp_E";
		let H0 := fresh in
		cut A;	
		[ intro H0; apply H in H0 | ];
		clear H; tauto1_ (S(d))

	| 			      |- ?A \/ ?B  => idtac d " : or_I1"; left; tauto1_ (S(d))
	| 			      |- ?A \/ ?B  => idtac d " : or_I2"; right; tauto1_ (S(d))
	| H: ?A \/ ?B |- _  	   => idtac d " : or_E"; destruct H; tauto1_ (S(d))
	| H: ?A /\ ?B |- _  	   => idtac d " : and_E"; destruct H; tauto1_ (S(d))
	|             |-  ?A /\ ?B => idtac d " : and_I"; split; tauto1_ (S(d))
	
  | _ => idtac d " : fail"; fail 
end.

Ltac tauto1 := tauto1_ 0.

Lemma t : False -> A. Proof. tauto1. Qed.
Lemma t2 : A /\ B -> A. Proof. tauto1. Qed.
Lemma t3 : A /\ B -> B. Proof. tauto1. Qed.
Lemma t4 : A /\ B -> B /\ A. Proof. tauto1. Qed.
Lemma t5 : A -> A \/ B. Proof. tauto1. Qed.
Lemma t6 : B -> B \/ A. Proof. tauto1. Qed.
Lemma t7 : (A -> C) -> (B -> C) -> A \/ B -> C. Proof. tauto1. Qed.
Lemma t8 : A -> (A -> B) -> B. Proof. tauto1. Qed.
Lemma t9 : A -> (A -> B) -> (B -> C) -> B. Proof. tauto1. Qed.
Lemma t10 : A -> (A -> B) -> (B -> C) -> C. Proof. tauto1. Qed.


(* 	"tauto2_ (S(d)) || fail 1" means we try "tauto2_ (S(d))" and if it fails (with level 0) we raise "fail 1". 
	When "fail 1" is raised, we go to the previous level without backtracking
*)

Ltac tauto2_ d := match goal with
	| 		 |- True 	   => idtac d " : trivial" ; trivial
	|_:?A 	 |- ?A 	 	   => idtac d " : assumption" ; assumption 
	|_:False |- _ 	 	   => idtac d " : contradiction" ; contradiction
	| 		 |- (?A -> ?B) => idtac d " : imp_I" ; intro;   tauto2_ (S(d)) || fail 1
	
	|H:(?A -> ?B) |- ?C  => 
		let H1 := fresh in
		idtac d " : imp_E";
		cut A;
		[ intro H1; apply H in H1 | ];
		clear H; tauto2_ (S(d))
	
	| 			  |- ?A \/ ?B => idtac d " : or_I1"; left; tauto2_ (S(d))
	| 			  |- ?A \/ ?B => idtac d " : or_I2"; right; tauto2_ (S(d))
	| H: ?A \/ ?B |- _  	  => idtac d " : or_E"; destruct H;  tauto2_ (S(d)) || fail 1
	|H: ?A /\ ?B  |- _  	  => idtac d " : and_E"; destruct H; tauto2_ (S(d)) || fail 1
	| 			  |- ?A /\ ?B => idtac d " : and_I"; split; tauto2_ (S(d)) || fail 1
	
	| _ => idtac d " : fail"; fail 
end.

Ltac tauto2 := tauto2_ 0.

(* Here we can see that the first test prints 2 times "fail" : 1 time when "A" fails
and the other when "A -> False" fails *)
Lemma test_backtrack1  : (A -> False) \/ True. Proof. tauto1. Qed. 
(* with "tauto1" we have only 1 backtrack : when "A" fails, we just go to the previous level without
backtracking*)
Lemma test_backtrack2 : (A -> False) \/ True. Proof. tauto2. Qed. 

(* here we can see that "tauto1" backtracks for each one of the "/\"   *)
Lemma b1 : ((A /\ (A /\ (A /\ A))) -> False) \/ True. 
Proof. tauto1. Qed.
(* with tauto2, "fail" is printed only once : for each nested "/\" we go up without backtracking.
	after "fail" is printed the next rule is applied at depth = 0  *)
Lemma b2 : ((A /\ (A /\ (A /\ A))) -> False) \/ True. 
Proof. tauto2. Qed.



(* Formalizing the tactic *)

Inductive form : Set :=
	| f_var 	: nat -> form 
	| f_true 	: form 
	| f_false   : form 
	| f_or  	: form -> form -> form
	| f_and 	: form -> form -> form 
	| f_imp 	: form -> form -> form.

Inductive seq : Set := 
	sequent : list form -> form -> seq.
		

Fixpoint form_eq (x y: form) : bool := 
	match x,y with 
	| f_true, f_true => true
	| f_false, f_false => true
	| f_var v1, f_var v2 =>  eqb v1 v2
	
	| f_or f1 f2 , f_or f1' f2' 
	| f_and f1 f2 , f_and f1' f2' 
	| f_imp f1 f2 , f_and f1' f2' 
	=> form_eq f1 f1' && form_eq f2 f2'
	
	| _,_ => false 
	end.

Definition in_form_list (x : form) (L: list form) : bool := 
match  List.find (form_eq x) L with 
	| Some _ => true
	| _ => false 
	end.

Definition is_leaf (s:seq) : bool := 
	match s with 
	| sequent _ f_true => true
	| sequent L A =>  in_form_list f_false L || in_form_list A L 
	end.

Eval compute in (is_leaf (sequent [] f_true)).
Eval compute in (is_leaf (sequent [] f_false)).
Eval compute in (is_leaf (sequent [f_var 0] (f_var 0))).
Eval compute in (is_leaf (sequent [f_var 1; f_var 2; f_var 0] (f_var 0))).
Eval compute in (is_leaf (sequent [f_var 1; f_var 2; f_false] (f_var 0))). (* true because "f_false" is in the premisses*)


(* Step *)

Definition subgoals := list (list seq).

Fixpoint pick_hyp_ (L1 L2: list form) := 
    match L2 with 
	| nil => nil
	| h :: t => (h,  L1++t ) :: pick_hyp_ (L1++[h]) t
    end.

Definition pick_hyp (s: seq) : list (form * list form) := 
    match s with 
	sequent L _ => pick_hyp_ nil L 
	end.

Eval compute in (pick_hyp (sequent [f_var 1; f_var 2; f_false] (f_var 0))).
Eval compute in (pick_hyp_ [f_var 1] [f_var 2; f_false] ).

Definition intro_rules l C := 
	match C with 
	| f_imp A B => [ [sequent (l++[A]) B]  ]
	| f_or  A B =>  [ [sequent l A]; [sequent l B] ]
	| f_and A B => [ [sequent l A; sequent l B] ]
	| _ => []
	end.

Definition elim_rules C hyp := 
	match hyp with 
	| (f_imp A B, l)  =>  [sequent (l++[B]) C; sequent l A]
	| (f_or  A B, l)  =>  [ sequent (l++[A]) C; sequent (l++[B]) C ]
	| (f_and A B, l)  => [sequent (l++[A;B]) C] 
	| _ => []
	end. 

Definition step (s : seq) : subgoals := 
	match s with sequent l C =>
	
	intro_rules l C ++ ( (map (elim_rules C) (pick_hyp s) ))
	end.

Eval compute in (step (sequent [f_or (f_var 0) (f_var 1); f_true] (f_imp (f_var 2) f_false ))).
Eval compute in (concat(step (sequent [f_or (f_var 0) (f_var 1); f_true] (f_imp (f_var 2) f_false )))).

Fixpoint tauto (d : nat) (s : seq) : bool := 
	match d with 
	| 0 => false
	| S n => 
		(* either the sequent is a leaf *)
		is_leaf s || 
		(* or there exists a goal such that all the generated premisses are valid *)
		(* "allValid seqs" returns true only if all the sequents in "seqs" are valid (in max detph "d") *) 
		let allValid (seqs:list seq) := forallb (tauto n) seqs in
		(* true if there exists a rule application such that all the generated subgoals are valid *)
		existsb allValid (step s)
	end.


(* Size of a formula *)
Fixpoint f_size (f : form) : nat := 
	match f with 
	| f_var _ | f_false | f_true => 0
	| f_or A B | f_and A B | f_imp A B => S (f_size A + f_size B )
	end.

(* Size of a sequent *)
Definition size (s:seq) : nat := 
	match s with 
	sequent l f => 
		list_sum (map f_size l) + f_size f  
	end.


(* Proving termination *)

Ltac unfold_Forall := 
	repeat (try apply Forall_nil; try apply Forall_cons; simpl; auto).
	
Ltac split_Forall := 
	repeat (try (rewrite concat_app); apply Forall_app; split; simpl; auto).
	  

Lemma map_nil : forall (x: A -> B), map x [] = [].
Proof.
	unfold map.
	reflexivity.
Qed.

Definition pre (f:form) '(f2,l) : form * list form :=  (f2,f::l).

Lemma pick_hyp_pre : forall f l1 l2, pick_hyp_ (f::l1) l2 = map (pre f) (pick_hyp_ l1 l2).
Proof.
	intros.
	revert f l1.
	induction l2.
	simpl.
	reflexivity.
	simpl.
	intros.
	rewrite IHl2.
	reflexivity.
Qed.
	

Lemma Forall_pre : forall l f n a, 
    Forall (fun s' : seq => size s' < n) (concat (map (elim_rules f) l))
    -> 
    Forall (fun s' : seq => size s' < f_size a + n) (concat (map (elim_rules f) (map (pre a) l))).
Proof.
	intros.
	rewrite map_map.
	induction l.
	
	all: simpl; auto.
	split_Forall.

	destruct a0.
	simpl; simpl in H.
	
	rewrite Forall_app in H; destruct H.
	destruct f0.
		1-3: simpl; auto.

		unfold_Forall.
		inversion H; simpl in H3; lia.
		inversion H; inversion H4; simpl in H7; lia.
		unfold_Forall.
		inversion H; simpl in H3; lia.
		unfold_Forall.
		inversion H; simpl in H3; lia.
		inversion H; inversion H4; simpl in H7; lia.
	
	apply IHl.
	simpl in H.
	rewrite Forall_app in H.
	destruct H.
	apply H0.
Qed.


Theorem decrease : forall (s:seq), Forall (fun s' => size s' < size s) (concat (step s)) .
Proof.
	
	destruct s.
	induction l.

	unfold step; split_Forall.

	destruct f.
	
	1-3: apply Forall_nil.
	1-3: unfold_Forall.
	1-5 : simpl; auto; lia.

	unfold step; split_Forall.
	destruct f; destruct a; unfold_Forall.
	
	all: try lia.
	1-6: try rewrite map_app; try rewrite list_sum_app; simpl; auto; lia.

	destruct a; unfold_Forall; simpl; auto.
	1-5: try rewrite map_app; try rewrite list_sum_app; simpl; auto; lia.
	
	rewrite pick_hyp_pre.
	simpl in IHl.
	rewrite concat_app in IHl; rewrite Forall_app in IHl; destruct IHl.
	rewrite <- plus_assoc.
	apply Forall_pre.
	apply H0.
Qed.

(* Proving Soundness *)

Definition prop_of_nat (n:nat) : Prop := 
forall (f : nat -> Prop), f n.

Fixpoint sem (f:form) : Prop := 
match f with
| f_true    => True
| f_false   => False
| f_var x   => prop_of_nat x
| f_or A B  => (sem A) /\ (sem B)
| f_and A B => (sem A) \/ (sem B)
| f_imp A B => (sem A) -> (sem B)
end.

Definition valid_seq (s:seq) : Prop :=
	match s with 
	sequent l f => Forall sem l -> sem f 
	end
.

Definition valid_sub (s:subgoals) : Prop :=
	Exists (Forall valid_seq) s 
.


(* We redefine "in_form_list" and "is_leaf" so they return a "Prop" instead of a "bool" *)

Definition in_form_list_prop (x : form) (L: list form) : Prop := In x L.

Definition is_leaf_prop (s:seq) : Prop := 
	match s with 
	| sequent _ f_true => True
	| sequent L A =>  in_form_list_prop f_false L \/ in_form_list_prop A L 
	end.

Lemma sound_leaf (s:seq) : is_leaf_prop s -> valid_seq s .
Proof.
	intro.
	destruct s.
	unfold is_leaf_prop in H.
	
	simpl in H.
	 
	destruct f; unfold valid_seq; unfold sem.
	unfold in_form_list_prop in H.
	destruct H.
	
	all: rewrite Forall_forall.
	
	intro; apply H0 in H.
	contradiction.
	
	intro; apply H0 in H.
	apply H.

	intro; trivial.
	
	destruct H.

	1-2: intro; apply H0 in H; apply H.

	intro. destruct H.
		apply H0 in H. contradiction.
		apply H0 in H. apply H.

	intro. destruct H.
		apply H0 in H. contradiction.
		apply H0 in H. apply H.

	intro. destruct H.
		apply H0 in H. contradiction.
		apply H0 in H. apply H.
	
Qed.