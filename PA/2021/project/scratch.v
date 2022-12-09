(* J'ai suivi le cours 2.7.1 (Foundations of proof systems), je n'avais jamais fait de Coq avant.
	Par contre j'ai eu un cours d'introduction à l'assistant de preuve "Isabelle" l'année dernière
*)

Require Import Ltac Bool List Nat Arith Lia.
Import ListNotations.

Ltac tauto1_ d := match goal with
	|  		  |- True       => idtac d ": trivial" ; trivial
	| _:?A 	  |- ?A 	       => idtac d ": assumption" ; assumption 
	| _:False |- _ 	 	   => idtac d ": contradiction" ; contradiction
	|  		  |- (?A -> ?B) => idtac d " : imp_I" ; intro; tauto1_ (S(d))

	|H:(?A -> ?B) |- ?C  => 
		let H1 := fresh in
		idtac d " : imp_E";
		cut A;
		[ intro H1; apply H in H1 | ];
		clear H; tauto1_ (S(d))

	| 			  |- ?A \/ ?B  => idtac d " : or_I1"; left; tauto1_ (S(d))
	| 			  |- ?A \/ ?B  => idtac d " : or_I2"; right; tauto1_ (S(d))
	| H: ?A \/ ?B |- _  	   => idtac d " : or_E"; destruct H; tauto1_ (S(d))
	| H: ?A /\ ?B |- _  	   => idtac d " : and_E"; destruct H; tauto1_ (S(d))
	|             |-  ?A /\ ?B => idtac d " : and_I"; split; tauto1_ (S(d))

	
	| _ => idtac d " : backtrack"; fail 
end.

Ltac tauto1 := tauto1_ 0.
Parameter A B C:Prop.

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

Lemma t7 : (A -> C) -> (B -> C) -> A \/ B -> C. 
Proof. tauto1. Qed.

Lemma t8 : A -> (A -> B) -> B. 
Proof. tauto1. Qed.

Lemma t9 : A -> (A -> B) -> (B -> C) -> B. 
Proof. tauto1. Qed.

Lemma t10 : A -> (A -> B) -> (B -> C) -> C. 
Proof. tauto1. Qed.


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
	
	| _ => idtac d " : backtrack"; fail 
end.

Ltac tauto2 := tauto2_ 0.

(* Here we can see that the first test prints 2 times "backtrack" : 1 time when "A" fails
and the other when "A -> False" fails *)
Lemma test_backtrack1  : (A -> False) \/ True. Proof. tauto1. Qed. 
(* with "tauto1" we have only 1 backtrack : when "A" fails, we just go to the previous level without
backtracking*)
Lemma test_backtrack2 : (A -> False) \/ True. Proof. tauto2. Qed. 

(* here we can see that "tauto1" backtracks for each one of the "/\"   *)
Lemma b1 : ((A /\ (A /\ (A /\ A))) -> False) \/ True. 
Proof. tauto1. Qed.
(* with tauto2, "backtrack" is printed only once : for each nested "/\" we go up without backtracking.
	after "backtrack" is printed the next rule is applied at depth = 0  *)
Lemma b2 : ((A /\ (A /\ (A /\ A))) -> False) \/ True. 
Proof. tauto2. Qed.



(* Formalizing the tactic *)
Inductive form : Set :=
	| f_var 	: nat -> form 
	| f_true 	: form 
	| f_false : form 
	| f_or  	: form -> form -> form
	| f_and 	: form -> form -> form 
	| f_imp 	: form -> form -> form.

Inductive seq : Set := 
	sequent : list form -> form -> seq.


Fixpoint form_eq (x y: form) : bool := 
	match x,y with 
	| f_true, f_true => true
	| f_false, f_false => true
	| f_var v1, f_var v2 => beq_nat v1 v2 
	
	| f_or f1 f2 , f_or f1' f2' 
	| f_and f1 f2 , f_and f1' f2' 
	| f_imp f1 f2 , f_and f1' f2' 
	=> form_eq f1 f1' && form_eq f2 f2'
	
	| _,_ => false 
	end.


Eval compute in (form_eq f_false (f_var 0)).
Eval compute in (form_eq f_false (f_var 0)).

Definition in_form_list (x : form) (L: list form) : bool := 
	match List.find (form_eq x) L with 
	| Some _ => true
	| _ => false 
	end.

Definition is_leaf (s:seq) : bool := 
	match s with 
	| sequent _ f_true => true
	| sequent L A =>  in_form_list f_false L || in_form_list A L 
	end
.

Eval compute in (is_leaf (sequent [] f_true)).
Eval compute in (is_leaf (sequent [] f_false)).
Eval compute in (is_leaf (sequent [f_var 0] (f_var 0))).
Eval compute in (is_leaf (sequent [f_var 1; f_var 2; f_var 0] (f_var 0))).
Eval compute in (is_leaf (sequent [f_var 1; f_var 2; f_false] (f_var 0))).

Definition subgoals := list (list seq).


Fixpoint pick_hyp_ (L1 L2: list form) := 
    match L2 with 
	| nil => nil
	| h :: t => (h, L1 ++ t ) :: pick_hyp_ (h::L1) t
    end.

Definition pick_hyp (s: seq) : list (form * list form) := 
    match s with 
	sequent L _ => pick_hyp_ nil L 
	end.

Eval compute in (pick_hyp (sequent [f_var 1; f_var 2; f_false] (f_var 0))).

Definition step (s : seq) : subgoals := 
	match s with sequent l C =>
		let intro := 
			(match C with 
			| f_imp A B => [ [sequent (l++[A]) B]  ]
			| f_or  A B =>  [ [sequent l A]; [sequent l B] ]
			| f_and A B => [ [sequent l A; sequent l B] ]
			| _ => []
			end)
		in 
	
	let elim C hyp := 
		(match hyp with 
		| (f_imp A B, l)  =>  [sequent (l++[B]) C; sequent l A]  
		| (f_or  A B, l)  =>  [ sequent (l++[A]) C; sequent (l++[B]) C ] 
		| (f_and A B, l)  => [sequent (l++[A;B]) C] 
		| _ => []
		end)
	in 
	
	intro ++ ( (map (elim C) (pick_hyp s) ))
	end	
.

Eval compute in (step (sequent [f_or (f_var 0) (f_var 1)] (f_imp (f_var 2) (f_var 3)))).


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
	| f_or A B | f_and A B | f_imp A B => f_size A + f_size B 
	end.

(* Size of a sequent *)
Definition size (s:seq) : nat := 
	match s with 
	sequent l f => 
		list_sum (map f_size l) + f_size f  
	end.




Definition smaller_than (s : seq) (seqs: list seq) := size s < list_sum (map size seqs).

Lemma map_on_nil : map f_size [] = [].
Proof.
	unfold map.
	reflexivity.
Qed.

Lemma or_size (f1 f2 : form) : f_size (f_or f1 f2) = f_size f1 + f_size f2.
Proof.
	unfold f_size.
	auto.
Qed.



Theorem decrease : forall (s:seq), Forall (smaller_than s) (step s).
Proof.
	destruct s.
	induction l.
	simpl; auto.
	unfold smaller_than.
	apply Forall_app.
	split.
	destruct f.
	apply Forall_nil.
	apply Forall_nil.
	apply Forall_nil.
	apply Forall_cons.
	unfold size.
	rewrite map_on_nil.
	rewrite or_size.
	unfold list_sum; simpl.
Admitted.

