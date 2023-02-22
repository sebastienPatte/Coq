Require Import definitions.
Require Import ZArith Arith Bool Lia.

Require Import bool_help.
Hint Resolve leb_complete : core. 
Hint Resolve leb_correct : core. 
Hint Resolve ltb_correct : core. 
Hint Resolve ltb_complete : core.
Hint Resolve Nat.ltb_lt : core.
Hint Resolve Nat.sub_0_r Nat.lt_le_incl ltb_imp_leb ltb_trans leb_trans ltb_leb_trans: core.


Lemma valid_b_more (p q : poly) (i:nat) : 
valid_b (Poly p i q) = true -> valid_b p = true /\ valid_b q = true.
Proof.
intro.
split.
induction p; simpl in H; intuition.
- destruct q.
elim (Z.eq_dec z 0); intro; destruct z; intuition; andb_destr H; intuition.
  andb_destr H.
  simpl.
  assumption.
- destruct p,q; simpl in H; intuition; andb_destr H; simpl; assumption.
Qed.

Lemma valid_b_more_r (p q1 q2 : poly) (n n0:nat) : 
valid_b (Poly p n (Poly q1 n0 q2)) = true -> valid_b (Poly p n q2) = true.
Proof.
intro.
simpl in H.
destruct p; destruct q2; andb_destr H.
- destruct q1; destruct z0; intuition.
- destruct q1; andb_destr H0; simpl; andb_split; try assumption; try apply leb_trans with (j:= n0); intuition.
- destruct q1; destruct z; simpl; intuition.
- destruct q1; andb_destr H0; simpl; andb_split; try assumption; try apply leb_trans with (j:= n0); intuition.
Qed.

Lemma valid_b_more_l (p1 p2 q : poly) (n n0:nat) : 
valid_b (Poly (Poly p1 n0 p2) n q) = true -> valid_b (Poly p1 n q) = true /\ valid_b (Poly p2 n q) = true.
Proof.
intro.
destruct p1;  destruct q; simpl in H; simpl.
- split; destruct z0; intuition; destruct p2; andb_destr H; try andb_split; intuition; apply ltb_leb_trans with (j:=n0); intuition.
- split; destruct p2; andb_split; andb_destr H; intuition.
  apply ltb_leb_trans with (j:=n0); intuition.
- split. 
  + destruct z; [intuition| |]; destruct p2. 
	destruct z; andb_destr H; [ inversion H0| |]; andb_split; intuition; apply ltb_trans with (j:=n0); intuition.
	andb_split; andb_destr H; [apply ltb_trans with (j:=n0)|]; intuition.
	andb_split; [ destruct z; andb_destr H; apply ltb_trans with (j:=n0)|]; intuition.
	destruct z; andb_destr H; [inversion H0| |]; intuition.
	andb_destr H; andb_split; [apply ltb_trans with (j:=n0)|]; intuition.
  + destruct p2. 
	destruct z; intuition.
	destruct z; intuition; andb_destr H; andb_split.
	1,3: apply ltb_leb_trans with (j:= n0); split; intuition.
	1-2: assumption.
- split. 
  + destruct p2. andb_destr H; destruct z; [intuition| |]; andb_destr H1; andb_split; intuition. 
	apply ltb_trans with (j:=n0); split; intuition.
	apply ltb_trans with (j:=n0); split; intuition.
	andb_split; andb_destr H; intuition.
	apply ltb_trans with (j:=n0); split; intuition.
  + destruct p2. andb_destr H; destruct z; [intuition| |]; andb_destr H1; andb_split; intuition.
	andb_split; andb_destr H; intuition.
	apply ltb_leb_trans with (j:=n0); split; intuition.
Qed.


Ltac is_valid := match goal with
| H:valid_b (Poly (Poly _ _ _) _ (Poly _ _ _)) = true |- valid_b (Poly _ _ _) = true =>
  idtac "match_lr"; 
  let t := type of H in idtac t;
  let H0 := fresh "V" in
  let H1 := fresh "V" in
  let V1 := fresh "V" in
  let V2 := fresh "V" in
  let V3 := fresh "V" in
  specialize H as H0; specialize H as H1;
  apply valid_b_more_l in H as [V1 V2];
  apply valid_b_more_r in H0 as V3;
  apply valid_b_more in H0 as V3; 
  assumption || is_valid V1 || is_valid V2 || is_valid V3  

| H:valid_b (Poly (_ _ _) _ ?q) = true |- valid_b (Poly _ _ ?q) = true =>
  idtac "match_l"; 
  let H1 := fresh "V" in
  let H2 := fresh "V" in
  apply valid_b_more_l in H as [H1 H2]; 
  assumption || is_valid H1 || is_valid H2

| H:valid_b (Poly ?p _ (_ _ _)) = true |- valid_b (Poly ?p _ _) = true =>
  idtac "match_r"; 
  let H1 := fresh "V" in
  apply valid_b_more_r in H as H1; 
  assumption || is_valid H1 

| H:valid_b (Poly _ _ _) = true |- valid_b ?p' = true => 
  idtac "match"; 
  let H1 := fresh H in
  let H2 := fresh H in
  apply valid_b_more in H as [H H']; 
  assumption || is_valid H1 || is_valid H2
end.

Ltac valid_destr H := 
let H0 := fresh "V" in specialize H as H0;  
match type of H0 with 
| valid_b (Poly (Poly _ _ _) _ (Poly _ _ _)) = true =>
  idtac "match"; 
  let H1 := fresh "V" in 
  let H2 := fresh "V" in 
  let V0 := fresh "V" in
  let V1 := fresh "V" in
  let V2 := fresh "V" in
  let V3 := fresh "V" in
  let V4 := fresh "V" in
  specialize H0 as H1; specialize H0 as H2; 
  apply valid_b_more in H0 as (V0 & V1); 
  apply valid_b_more_l in H1 as (V2 & V3);
  apply valid_b_more_r in H2 as V4

| valid_b (Poly _ _ (Poly _ _ _)) = true  => 
  idtac "match_r"; 
  let H1 := fresh "V" in
  let V0 := fresh "V" in
  let V1 := fresh "V" in
  let V2 := fresh "V" in
  specialize H0 as H1; 
  apply valid_b_more in H0 as (V0 & V1); 
  apply valid_b_more_r in H1 as V2

| valid_b (Poly (Poly _ _ _) _ _) = true  =>
  idtac "match_l"; 
  let H1 := fresh "V" in
  let V0 := fresh "V" in
  let V1 := fresh "V" in
  let V2 := fresh "V" in
  specialize H0 as H1; 
  apply valid_b_more in H0 as (V0 & V1); 
  apply valid_b_more_l in H1 as (H1 & V2)
  

| valid_b (Poly _ _ _) = true  => 
  idtac "match"; 
  let H1 := fresh "V" in
  let H2 := fresh "V" in
  apply valid_b_more in H0 as (H1 & H2) 
end.

Lemma le_valid (p p' q q' : poly) (i j:nat)  : 
i>j -> 
valid_b (Poly p i q) = true ->
valid_b (Poly p' j q') = true -> 
valid_b (Poly (Poly p i q) j q') = true.
Proof.
intros.
simpl in *.
destruct p.
- destruct p'.
  + destruct q'.
	* destruct z1; [inversion H1| |];  andb_split; intuition.
	* andb_destr H1.  andb_split; intuition.
  +  destruct q'. 
	* destruct z0; [inversion H1| |];  andb_split; intuition.
	* andb_destr H1.  andb_split; intuition.
- destruct p'.
  + destruct q'.
	* destruct z0; [inversion H1| |];  andb_split; intuition.
	* andb_destr H1. andb_split; intuition.
  +  destruct q'. 
	* destruct z; [inversion H1| |];  andb_split; intuition.
	* andb_destr H1.  andb_split; intuition.
Qed.


Lemma valid_le (p q1 q2:poly) (i j:nat) : valid_b (Poly (Poly p i q1) j q2) = true -> j < i.
Proof.
intro.
simpl in H.
destruct q2.
- destruct z; [inversion H| |]; andb_destr H; apply ltb_complete; assumption.
- andb_destr H; apply ltb_complete; assumption.
Qed.

Lemma valid_leq (p q1 q2:poly) (i j:nat) : valid_b (Poly p i (Poly q1 j q2) )  = true -> i <= j.
Proof.
intro.
simpl in H.
destruct p; andb_destr H; apply leb_complete; assumption.
Qed.



Lemma leq_valid (p p' q q' : poly) (i j:nat)  : 
i <= j -> 
valid_b (Poly p i q) = true ->
valid_b (Poly p' j q') = true -> 
valid_b (Poly p i (Poly p' j q')) = true.
Proof.
intros.
simpl in *.
destruct p,q.
- andb_split. auto. assumption.
- andb_split. auto. assumption.
- destruct z; [inversion H0| |]; andb_destr H0; andb_split; auto. 
- andb_destr H0. andb_split; auto.
Qed.

(* For any polynom [Poly p i (Cst z)] the constant [z] is not 0 *)
Lemma valid_not0 (p:poly) (i:nat) (z:Z) : valid_b (Poly p i (Cst z))  = true -> z <> 0%Z.
Proof.
intro.
simpl in H.
destruct p; destruct z; intuition.
Qed.

Fixpoint weak_valid_b (pol:poly) : bool := 
  match pol with
  |Cst _ => true
  |Poly p i q => 
    match p,q with 
    | (Cst _), (Cst _) => true 
    | (Poly _ j1 _), (Cst _) => (i <? j1) && weak_valid_b p 
    | (Cst _),  (Poly p2 j2 q2) => (i <=? j2) && weak_valid_b q 
    |(Poly p1 j1 q1),  (Poly p2 j2 q2) => 
      (i <? j1) && (i <=? j2) 
      && weak_valid_b p 
      && weak_valid_b q
    end 
  end
.



Lemma weaken_valid (p:poly) (H:valid_b p = true) : weak_valid_b p = true.
Proof.
  induction p.
  - simpl. reflexivity.
  - valid_destr H.
    specialize (IHp1 V0).
    specialize (IHp2 V1).
    simpl in *.
    destruct p1.
    * destruct p2.
      destruct z0; reflexivity.
      andb_split. andb_destr H. assumption.
      assumption.
    * destruct p2.
      destruct z. inversion H.  
      1-3 : andb_destr H; andb_split; assumption.
Qed.

Lemma weak_valid_le (p q1 q2:poly) (i j:nat) : weak_valid_b (Poly (Poly p i q1) j q2) = true -> j < i.
Proof.
  intro.
  simpl in H.
  destruct q2.
  - destruct z; [inversion H| |]; andb_destr H; apply ltb_complete; assumption.
  - andb_destr H; apply ltb_complete; assumption.
Qed.

Lemma weak_valid_leq (p q1 q2:poly) (i j:nat) : weak_valid_b (Poly p i (Poly q1 j q2) )  = true -> i <= j.
Proof.
  intro.
  simpl in H.
  destruct p; andb_destr H; apply leb_complete; assumption.
Qed.

Lemma weak_valid_b_more (p q : poly) (i:nat) : 
  weak_valid_b (Poly p i q) = true -> weak_valid_b p = true /\ weak_valid_b q = true.
Proof.
  intro.
  split.
  induction p; simpl in H; intuition.
  - destruct q.
  elim (Z.eq_dec z 0); intro; destruct z; intuition; andb_destr H; intuition.
    andb_destr H.
    simpl.
    assumption.
  - destruct p,q; simpl in H; intuition; andb_destr H; simpl; assumption.
Qed.


Lemma weak_valid_b_more_r (p q1 q2 : poly) (n n0:nat) : 
  weak_valid_b (Poly p n (Poly q1 n0 q2)) = true -> weak_valid_b (Poly p n q2) = true.
Proof.
  intro.
  simpl in H.
  destruct p; destruct q2; andb_destr H.
  - destruct q1; destruct z0; intuition.
  - destruct q1; andb_destr H0; simpl; andb_split; try assumption; try apply leb_trans with (j:= n0); intuition.
  - destruct q1; destruct z; simpl; intuition.
  - destruct q1; andb_destr H0; simpl; andb_split; try assumption; try apply leb_trans with (j:= n0); intuition.
Qed.

Lemma weak_valid_b_more_l (p1 p2 q : poly) (n n0:nat) : 
  weak_valid_b (Poly (Poly p1 n0 p2) n q) = true -> weak_valid_b (Poly p1 n q) = true /\ weak_valid_b (Poly p2 n q) = true.
Proof.
  intro.
  destruct p1;  destruct q; simpl in H; simpl.
  - split; destruct z0; intuition; destruct p2; andb_destr H; try andb_split; intuition; apply ltb_leb_trans with (j:=n0); intuition.
  - split; destruct p2; andb_split; andb_destr H; intuition.
    apply ltb_leb_trans with (j:=n0); intuition.
  - split. 
    +  destruct p2; 
      andb_destr H; andb_split.  apply ltb_trans with (j:=n0); intuition. 
      assumption. apply ltb_trans with (j:=n0); intuition. assumption.
    + destruct p2. 
      trivial.
      andb_destr H; andb_split.
      apply ltb_leb_trans with (j:= n0); split; intuition.
      assumption.
  - split. 
    +  destruct p2; andb_destr H; andb_destr H1; andb_split; intuition. 
      apply ltb_trans with (j:=n0); split; intuition.
      apply ltb_trans with (j:=n0); split; intuition.
    + destruct p2; andb_destr H; andb_destr H1; andb_split; intuition.
      apply ltb_leb_trans with (j:=n0); split; intuition.
Qed.


Ltac weak_valid_destr H := 
  let H0 := fresh "V" in specialize H as H0;  
  match type of H0 with 
  | weak_valid_b (Poly (Poly _ _ _) _ (Poly _ _ _)) = true =>
    idtac "match"; 
    let H1 := fresh "V" in 
    let H2 := fresh "V" in 
    let V0 := fresh "V" in
    let V1 := fresh "V" in
    let V2 := fresh "V" in
    let V3 := fresh "V" in
    let V4 := fresh "V" in
    specialize H0 as H1; specialize H0 as H2; 
    apply weak_valid_b_more in H0 as (V0 & V1); 
    apply weak_valid_b_more_l in H1 as (V2 & V3);
    apply weak_valid_b_more_r in H2 as V4

  | weak_valid_b (Poly _ _ (Poly _ _ _)) = true  => 
    idtac "match_r"; 
    let H1 := fresh "V" in
    let V0 := fresh "V" in
    let V1 := fresh "V" in
    let V2 := fresh "V" in
    specialize H0 as H1; 
    apply weak_valid_b_more in H0 as (V0 & V1); 
    apply weak_valid_b_more_r in H1 as V2

  | weak_valid_b (Poly (Poly _ _ _) _ _) = true  =>
    idtac "match_l"; 
    let H1 := fresh "V" in
    let V0 := fresh "V" in
    let V1 := fresh "V" in
    let V2 := fresh "V" in
    let V3 := fresh "V" in
    specialize H0 as H1; 
    apply weak_valid_b_more in H0 as (V0 & V1); 
    apply weak_valid_b_more_l in H1 as (V2 & V3)

  | weak_valid_b (Poly _ _ _) = true  => 
    idtac "match"; 
    let H1 := fresh "V" in
    let H2 := fresh "V" in
    apply weak_valid_b_more in H0 as (H1 & H2) 
end.



Lemma le_weak_valid (p p' q q' : poly) (i j:nat)  : 
i>j -> 
weak_valid_b (Poly p i q) = true ->
weak_valid_b (Poly p' j q') = true -> 
weak_valid_b (Poly (Poly p i q) j q') = true.
Proof.
  intros.
  simpl in *.
  destruct p.
  - destruct p'.
    + destruct q'.
      *  andb_split; intuition.
      * andb_destr H1.  andb_split; intuition.
    +  destruct q'. 
      * andb_split; intuition.
      * andb_destr H1.  andb_split; intuition.
  - destruct p'.
    + destruct q'.
      *  andb_split; intuition.
      * andb_destr H1. andb_split; intuition.
    +  destruct q'. 
      * andb_split; intuition.
      * andb_destr H1.  andb_split; intuition.
Qed.

Lemma leq_weak_valid (p p' q q' : poly) (i j:nat)  : 
i<=j -> 
weak_valid_b (Poly p i q) = true ->
weak_valid_b (Poly p' j q') = true -> 
weak_valid_b (Poly p i (Poly p' j q')) = true.
Proof.
  intros.
  simpl in *.
  destruct p.
  - destruct p'.
    + destruct q'.
      * andb_split; intuition.
      * andb_destr H1.  andb_split; intuition.
    +  destruct q'. 
      * andb_destr H1. andb_split; intuition.
      * andb_destr H1.  andb_split; intuition.
  - destruct p'.
    + destruct q'.
      * destruct q; andb_destr H0; andb_split; intuition.
      * andb_destr H1; destruct q; andb_destr H0; andb_split; intuition.
    +  destruct q'. 
      * andb_destr H1. destruct q; andb_destr H0; andb_split; intuition.
      * andb_destr H1. destruct q; andb_destr H0; andb_split; intuition.
Qed.