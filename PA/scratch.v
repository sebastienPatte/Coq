Require Import Arith Extraction.
Set Printing All.

Print True.
Print unit.

Print True_ind.
Print unit_ind.
About True_rect.

Definition True_rect_dep (P:True -> Type) (pi : P I) (p:True) : P I :=
	match p with 
	|I => pi
	end.

Print and.
Print prod.
Print True_rect.

Lemma markov_easy (f : nat -> Prop) :  (sig (fun n => f n = True)) -> (ex (fun n => f n = True)).
Proof.
	intro.
	destruct H.
	exists x.
	apply e.
Qed.

Section Markov.

Variable P : nat ->  bool .

Hypothesis exP : exists n : nat, P n = true.

Inductive acc_nat (i : nat) : Prop :=
	AccNat0 : P i = true -> acc_nat i
  | AccNatS : acc_nat (S i) -> acc_nat i.
	
Lemma acc_nat_plus : forall x n : nat,P (x + n) = true -> acc_nat n.
Proof.
	intros.
	induction x as [|x' Hx'] in n,H |-*.
	apply AccNat0.
	apply H.
	apply AccNatS.
	apply Hx'.
	rewrite <- plus_Snm_nSm.
	apply H.
Qed.
	
Search (  _ + _ = _ + _).
	
	