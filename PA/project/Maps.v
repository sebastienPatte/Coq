Require Import definitions.
Require Import BoolHelp.
Import ZArith Arith Bool Lia.
Import FMapList NatMap P F Coq.FSets.FMapFacts.
Require Import Valid.

Lemma eq_map_add_add (i x y :nat) (m:monoid) : Equal (add i x m) (add i x (add i y m)).
Proof.
  unfold Equal.
  intros.
  elim (Nat.eq_dec i y0); intro.
  - rewrite F.add_eq_o; [|assumption]. 
	rewrite F.add_eq_o; [|assumption].
	reflexivity.
  - rewrite F.add_neq_o; [|assumption]. 
	rewrite F.add_neq_o; [|assumption]. 
	rewrite F.add_neq_o; [|assumption].
	reflexivity.
Qed.

Lemma eq_map_add_each (i x :nat) (m1 m2:monoid) : Equal m1 m2 -> Equal (add i x m1) (add i x m2).
Proof.
  unfold Equal.
  intros.
  elim (Nat.eq_dec i y); intro.
  - rewrite F.add_eq_o; [|assumption]. 
	rewrite F.add_eq_o; [|assumption].
	reflexivity.
  - rewrite F.add_neq_o; [|assumption]. 
	rewrite F.add_neq_o; [|assumption]. 
	apply H.
Qed.

Lemma eq_map_add_remove (i x :nat) (m:monoid) : Equal (add i x m) (add i x (NatMap.remove i m)).
Proof.
  unfold Equal.
  intros.
  elim (Nat.eq_dec i y); intro.
  - rewrite F.add_eq_o; [|assumption]. 
	rewrite F.add_eq_o; [|assumption].
	reflexivity.
  - rewrite F.add_neq_o; [|assumption]. 
	rewrite F.add_neq_o; [|assumption]. 
	rewrite F.remove_neq_o; [|assumption].
	reflexivity.
Qed.

Lemma eq_map_add_same_in (i n :nat) (m:monoid) : NatMap.find i m = Some n ->  Equal m (add i n m) .
Proof.
  unfold Equal.
  intros.
  elim (Nat.eq_dec i y); intro.
  - rewrite <- a. rewrite F.add_eq_o; intuition.
  - rewrite F.add_neq_o; intuition.
Qed.

Lemma eq_map_add_swap (i j x y :nat) (m:monoid) : i <> j -> Equal (add i x (add j y m)) (add j y (add i x m)).
Proof.  
  unfold Equal.
  intros.
  elim (Nat.eq_dec i y0); intro.
  - rewrite F.add_eq_o; [|intuition].
	rewrite F.add_neq_o; [|intuition].
	rewrite F.add_eq_o; [|intuition].
	reflexivity.
  - rewrite F.add_neq_o; [|intuition].
	elim (Nat.eq_dec j y0); intro.
	+ rewrite F.add_eq_o; [|intuition].
	  rewrite F.add_eq_o; [|intuition].
	  reflexivity.
	+ rewrite F.add_neq_o; [|intuition].
	  rewrite F.add_neq_o; [|intuition].
	  rewrite F.add_neq_o; [|intuition].
	  reflexivity.
Qed.

Lemma for_all_eq_map (m1 m2 :monoid) : Equal m1 m2 -> P.for_all (fun _ v : nat => v =? 0) m1 = P.for_all (fun _ v : nat => v =? 0) m2.
Proof.
  intro.
  unfold P.for_all.
  rewrite P.fold_Equal with (m2:=m2).
  - intuition.
  - intuition.
  - intuition.
  - unfold P.transpose_neqkey.
	intros.
	destruct e,e'; intuition.
  - assumption.
Qed.

Lemma find_eq_map (m1 m2 :monoid) (x:nat) : Equal m1 m2 -> NatMap.find x m1 = NatMap.find x m2.
Proof.
  apply F.find_m; intuition.
Qed. 


Lemma for_all_add_0_notin (m:monoid) (i:nat) :
NatMap.find i m = None -> P.for_all (fun _ v : nat => v =? 0) m = P.for_all (fun _ v : nat => v =? 0) (add i 0 m).
Proof.
  intro.
  unfold P.for_all.
  rewrite P.fold_add.
  - simpl. reflexivity.
  - intuition.
  - intuition.
  - unfold P.transpose_neqkey; intros; destruct e,e'; intuition.
  - rewrite F.not_find_in_iff; assumption.
Qed.

Lemma for_all_remove (m:monoid) (n:nat) : P.for_all (fun _ v : nat => v =? 0) m = true -> P.for_all (fun _ v : nat => v =? 0) (NatMap.remove n m) = true.
Proof.
  intros.
  unfold P.for_all.
  apply P.fold_rec_nodep.
  - trivial.
  - intros.
	rewrite P.for_all_iff in H; [|intuition].
	elim (Nat.eq_dec k n); intro.
	+ specialize (H k e). rewrite a0 in H0. rewrite F.remove_mapsto_iff in H0. destruct H0. contradiction (H0 eq_refl). 
	+ specialize (H k e). rewrite H1. rewrite F.remove_mapsto_iff in H0. destruct H0 as [_ H0]. specialize (H H0). rewrite H. reflexivity.
Qed.

Lemma for_all_add_0 (m:monoid) (i:nat) : P.for_all (fun _ v : nat => v =? 0) m = true -> P.for_all (fun _ v : nat => v =? 0) (add i 0 m) = true.
Proof.
  intros.
  rewrite for_all_eq_map with (m2:= add i 0 (NatMap.remove i m)).
  - erewrite <- for_all_add_0_notin.
	+ apply for_all_remove; assumption.
	+ rewrite F.remove_eq_o; intuition.
  - apply eq_map_add_remove.
Qed.

Local Definition for_all_add_S_notin (m:monoid) (i n:nat) :
NatMap.find i m = None -> P.for_all (fun _ v : nat => v =? 0) (add i (S n) m) = false.
Proof.
  intro.
  unfold P.for_all.
  rewrite P.fold_add.
  - simpl. reflexivity.
	- intuition.
	- intuition.
	- unfold P.transpose_neqkey. 
	  intuition.
	  destruct e,e'; intuition.
	- rewrite F.not_find_in_iff; assumption.
Qed.


Lemma for_all_add_S  (m:monoid) (i n:nat) :  P.for_all (fun _ v : nat => v =? 0) (add i (S n) m) = false.
Proof.
  rewrite for_all_eq_map with (m2:= add i (S n) (NatMap.remove i m)).
  - apply for_all_add_S_notin.
	apply F.remove_eq_o; reflexivity. 
  - rewrite eq_map_add_remove; reflexivity.
Qed.

Lemma for_all_add_add (m:monoid) (n0 n1 i: nat) :  P.for_all (fun _ v : nat => (v =? 0)%nat) (add i n1 (add i n0 m)) = P.for_all (fun _ v : nat => (v =? 0)%nat) (add i n1 m).
Proof.
  rewrite for_all_eq_map with (m2:= add i n1 m).
  - reflexivity.
  - rewrite <- eq_map_add_add; reflexivity.
Qed. 

Lemma for_all_exist_pos  (m:monoid) : (exists (n' r:nat), NatMap.find n' m = Some r /\ r <> 0) ->  P.for_all (fun _ v : nat => v =? 0) m = false.
Proof.
  intro.
  do 3 destruct H. 
  destruct x0; [contradiction|].
  rewrite for_all_eq_map with (m2 := add x (S x0) m).
  - apply for_all_add_S.
  - unfold Equal.
	intros.
	elim (Nat.eq_dec x y); intro.
	+ rewrite a in *. 
	  rewrite F.add_eq_o; intuition.
	+ rewrite F.add_neq_o; [|assumption].
	  reflexivity.
Qed.


Lemma get_coeff_eq_map (m1 m2:monoid)  (p:poly) : valid_b p = true -> 
Equal m1 m2 ->
get_coefficient_ p m1 = get_coefficient_ p m2.
Proof.
  intro.
  revert m2.
  revert m1.
  induction p; intros.
  - simpl.
	rewrite for_all_eq_map with (m2:=m2); intuition.
  - valid_destr H. 
	specialize (IHp1 V0).
	specialize (IHp2 V1).
	simpl.
	specialize H0 as Heq.
	unfold Equal in H0.
	rewrite (H0 n).
	destruct (NatMap.find (elt:=nat) n m2).
	+ rewrite (IHp1 m1 m2 Heq). 
	  destruct n0; [reflexivity|].
	  simpl; rewrite Nat.sub_0_r.
	  rewrite (IHp2 (add n n0 m1) (add n n0 m2)).
	  * reflexivity.
	  * apply eq_map_add_each; apply Heq.
	+ apply (IHp1 m1 m2 Heq).
Qed.

Lemma get_coeff_add_add (i x y :nat) (m:monoid)  (p:poly) : valid_b p = true -> get_coefficient_ p (add i x m) = get_coefficient_ p (add i x (add i y m)).
Proof.
  intro.
  erewrite get_coeff_eq_map with (m2:=(add i x (add i y m))). 
  - reflexivity.
  - assumption.
  - rewrite <- eq_map_add_add. reflexivity. 
Qed.