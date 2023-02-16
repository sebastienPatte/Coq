Require Import ZArith Bool Lia.

Inductive poly : Type :=
| Cst : Z -> poly
| Poly : poly -> nat -> poly -> poly .

Inductive valid_poly : poly -> Prop := 
|cst : forall (z:Z), valid_poly (Cst z)  
|compose_cst : 
	forall (i :nat), 
	forall (x y :Z), y <> 0%Z ->  
	valid_poly (Poly (Cst x) i (Cst y)) 
|compose_l : 
	forall (i j :nat), i < j ->
	forall (x :Z),  x <> 0%Z -> 
	forall (p q : poly), valid_poly (Poly p j q) -> 
	valid_poly (Poly (Poly p j q) i (Cst x)) 
|compose_r : 
	forall (i j :nat), i <= j ->
	forall (x :Z),  
	forall (p q : poly), valid_poly (Poly p j q) -> 
	valid_poly (Poly (Cst x) i (Poly p j q)) 
|compose_lr : 
	forall (i j j':nat), i < j /\ i <= j' ->
	forall (p q p' q': poly), valid_poly (Poly p j q) /\ valid_poly (Poly p' j' q') -> 
	valid_poly (Poly (Poly p j q) i (Poly p' j' q'))
.

Fixpoint valid_b (pol:poly) : bool := 
match pol with 
|Cst _ => true
|Poly p i q => 
  match p,q with 
| _, (Cst 0) => false 
| (Cst _), (Cst _) => true 
| (Poly _ j1 _), (Cst _) => 
	Nat.ltb i j1 
  && valid_b p 
| (Cst _),  (Poly p2 j2 q2) => 
	Nat.leb i j2 
  && valid_b q 
|(Poly p1 j1 q1),  (Poly p2 j2 q2) => 
  Nat.ltb i j1 && Nat.leb i j2 
  && valid_b p 
  && valid_b q
  end 
end.

Ltac andb_destr H := 
  repeat (let H' := fresh H in apply andb_true_iff in H as [H H']; try andb_destr H').

Ltac andb_split := 
  repeat (apply andb_true_iff; split).

Lemma ltb_correct (a b:nat) : a < b -> a<? b = true.
  apply Nat.ltb_lt; assumption.
Qed.
Lemma ltb_complete (a b:nat) : a<? b = true -> a < b.
  apply Nat.ltb_lt; assumption.
Qed.

Hint Resolve leb_complete : core. 
Hint Resolve leb_correct : core. 
Hint Resolve ltb_correct : core. 
Hint Resolve ltb_complete : core.
Hint Resolve Nat.ltb_lt : core.

Lemma option_dec {A}: 
  forall (el: option A),
    el = None \/ exists w: A, el = Some w.
Proof.
  intros.
  destruct el.
  right; exists a; trivial.
  left; trivial.
Qed.

Lemma poly_eq_dec (p1 p2 q1 q2:poly) (i:nat) : 
p1=p2 /\ q1=q2 ->   
(Poly p1 i q1) = (Poly p2 i q2)
.
Proof.
  intro.
  destruct H.
  rewrite H.
  rewrite H0.
  reflexivity.
Qed.

Lemma ltb_trans (i j n :nat) : (i <? j) = true /\ (j <? n) = true -> (i <? n) = true.
Proof.
  intros.
  destruct H.
  rewrite Nat.ltb_lt in H.
  rewrite Nat.ltb_lt in H0.
  rewrite Nat.ltb_lt.
  eapply Nat.lt_trans with (m:= j); assumption.
Qed.

Lemma leb_trans (i j n :nat) : (i <=? j) = true /\ (j <=? n) = true -> (i <=? n) = true.
Proof.
  intros.
  destruct H.
  rewrite Nat.leb_le in H.
  rewrite Nat.leb_le in H0.
  rewrite Nat.leb_le.
  eapply Nat.le_trans with (m:= j); assumption.
Qed.

Lemma ltb_leb_trans (i j n :nat) : (i <? j) = true /\ (j <=? n) = true -> (i <? n) = true.
Proof.
  intros.
  destruct H.
  rewrite Nat.ltb_lt in H.
  rewrite Nat.leb_le in H0.
  rewrite Nat.ltb_lt.
  apply Nat.lt_le_trans with (m:= j); assumption.
Qed.


Check Nat.lt_le_incl.

Lemma ltb_leb_incl (i j :nat) : (i <? j) = true -> (i <=? j) = true.
Proof.
  rewrite Nat.ltb_lt.
  rewrite Nat.leb_le.
  apply Nat.lt_le_incl.
Qed.

Hint Resolve Nat.sub_0_r ltb_trans leb_trans ltb_leb_trans: core.

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
    let H1 := fresh "V" in
    let H2 := fresh "V" in
    let H3 := fresh "V" in
    apply valid_b_more_l in H as [H1 H2];
    apply valid_b_more_r in H as H3; 
    assumption || is_valid H1 || is_valid H2 || is_valid H3  

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
  let H' := fresh "V" in specialize H as H';  
  match type of H' with 
  | valid_b (Poly (Poly _ _ _) _ (Poly _ _ _)) = true  =>
    idtac "match_lr"; 
    let t := type of H in idtac t;
    let H1 := fresh "V" in
    let H2 := fresh "V" in
    let H3 := fresh "V" in
    apply valid_b_more_l in H' as [H1 H2];
    apply valid_b_more_r in H' as H3 

  | valid_b (Poly _ _ (Poly _ _ _)) = true  => 
    idtac "match_r"; 
    let H1 := fresh "V" in
    apply valid_b_more_r in H' as H1
    

  | valid_b (Poly (Poly _ _ _) _ _) = true  =>
    idtac "match_l"; 
    let H1 := fresh "V" in
    let H2 := fresh "V" in
    apply valid_b_more_l in H' as [H1 H2]

  | valid_b (Poly _ _ _) = true  => 
    idtac "match"; 
    let H1 := fresh "V" in
    let H2 := fresh "V" in
    apply valid_b_more in H' as [H1 H2] 
end.


Goal valid_b (Poly (Poly (Cst 0) 1 (Cst 1)) 0 (Poly (Cst 0) 1 (Cst 1))) =true -> valid_b (Cst 1) =true.
intro.
 valid_destr H.
Abort.

Lemma poly_equivalence (p:poly) : valid_b p = true <-> valid_poly p.
Proof.
  unfold iff. split; intro.
  - induction p.
    + constructor.
    + destruct p1,p2; simpl in H; andb_destr H; constructor.
      * intro. rewrite H0 in H. inversion H. 
      * intuition.
      * destruct z; andb_destr H; intuition.
      * destruct z; andb_destr H; intuition.
      * intro. rewrite H0 in H. inversion H.
      * destruct z; andb_destr H; intuition.
      * split; intuition.
      * split; intuition.
  - induction p; inversion H.
    + intuition.
    + destruct y; intuition. 
    + rewrite <- H0 in *. rewrite <- H2 in *. 
      specialize (IHp1 H5). 
      simpl in *.
      destruct x; andb_split; intuition.
    + rewrite <- H0 in *. rewrite <- H3 in *.
      specialize (IHp2 H4).
      destruct x; andb_split; intuition.
    + rewrite <- H0 in *. rewrite <- H3 in *.
      destruct H2. destruct H4.
      specialize (IHp1 H4).
      specialize (IHp2 H6).
      simpl; andb_split; intuition.
Qed.


Definition p1 := (Poly (Cst 0) 2 (Cst 1)).

Record valid_pol : Type :=
{ VP_value : poly ;
VP_prop : valid_b VP_value = true }.

Section Bool_irrel.

  Let b_dec : forall (b1 b2 : bool), b1 = b2 \/ b1 <> b2.
  Proof.
    intros.
    elim (bool_dec b1 b2); intro; intuition.
  Qed.

  Let comp [A] [x y y':A] (eq1:x = y) (eq2:x = y') : y = y' :=
    eq_ind _ (fun a => a = y') eq2 _ eq1.

  Let trans_sym_eq [A] (x y:A) (u:x = y) : comp u u = eq_refl y.
  Proof.
    case u; trivial.
  Qed.

  Let nu [x y:bool] (u:x = y) : x = y :=
  match b_dec x y with     
    | or_introl eqxy => eqxy 
    | or_intror neqxy => False_ind _ (neqxy u)
  end.

  Let nu_constant [x y:bool] (u v:x = y) : nu u = nu v.
    unfold nu.
    destruct (b_dec x y) as [Heq|Hneq].
    - reflexivity.
    - case Hneq; trivial.
  Qed.

  Let nu_inv [x y:bool] (v:x = y) : x = y := comp (nu (eq_refl x)) v.

  Let nu_left_inv [x y:bool] (u:x = y) : nu_inv (nu u) = u.
  Proof.
    case u; unfold nu_inv.
    case eq_refl.
    apply trans_sym_eq.
  Qed.

  Lemma bool_irrel (x y:bool) (p1 p2:x = y) : p1 = p2.
  Proof.
    elim (nu_left_inv p1).
    elim (nu_left_inv p2).
    elim nu_constant with x y p1 p2.
    reflexivity.
  Qed.

  Eval compute in (comp (nu (eq_refl))).

End Bool_irrel.


Lemma leibniz : forall (p q : valid_pol), VP_value p = VP_value q -> p=q.
Proof.
  intros.
  destruct p.
  destruct q.  
  simpl in H.
  subst.
  apply f_equal.
  apply bool_irrel.
Qed.

(* https://cstheory.stackexchange.com/questions/5158/prove-proof-irrelevance-in-coq *)
(* https://www.di.ens.fr/~quyen/publication/ly10.pdf 
https://github.com/fblanqui/color/blob/1e7b26553c1ca94c787ad5a1b938acabb8d47f2f/Util/Polynom/Polynom.v
*)

(* 3 X0 X1 + 2 X0 X0 + 1 *)
Definition poly1 := (Poly (Cst 1%Z) 0 (Poly (Poly (Cst 0%Z) 1 (Cst 3%Z)) 0 (Cst 2%Z))).

Require Import FMapList.
Require Import Coq.FSets.FMapList.
Require Import Coq.Structures.OrderedTypeEx.
Module Import NatMap := FMapList.Make(Nat_as_OT).


Definition monoid : Type := NatMap.t nat.

(* We could make a single definition [get_coefficient] with a dependent match to keep the polynomials proofs of validity at each recursive call, but it makes the proofs harder. Instead we use the following definitions, with the lemma [valid_b_more] to propagate the polynomials validity proofs at each recursive call *)
Require Import
  Coq.FSets.FMapFacts.

  Module P := WProperties_fun Nat_as_OT NatMap.
  Module F := P.F.

Fixpoint get_coefficient_ (pol: poly) (m:monoid) := 
  match pol with 
  | Cst z => if (P.for_all (fun (k:nat) (v:nat) => v =? 0%nat ) m) then z else 0%Z 
  | Poly p i q => 
    match NatMap.find i m with 
      |None | Some 0 => get_coefficient_ p m
      |Some n => Z.add (get_coefficient_ p m) (get_coefficient_ q (add i (n-1) m))
      end
end.

Definition get_coefficient (pol: valid_pol) (m:monoid) := get_coefficient_ (VP_value pol) m.

(* X0 X1 *)
Definition mymap := NatMap.add 0 1 (NatMap.add 1 1 (NatMap.empty nat)).

(* X0 + 1 *)
Definition poly2 := (Poly (Cst 1%Z) 0 (Cst 1%Z)).
(* X0 *)
Definition mymap2 := NatMap.add 0 1 ((NatMap.empty nat)).


Eval compute in (NatMap.find 0 (NatMap.add 0 2 (NatMap.add 0 1 (NatMap.empty nat)))).

Eval compute in (get_coefficient_ poly1 mymap).
Eval compute in (get_coefficient_ poly2 mymap2).
Eval compute in (get_coefficient_ poly1 (NatMap.empty nat)).
Eval compute in (get_coefficient_ poly2 (NatMap.empty nat)).

Definition empty_mono : monoid := NatMap.empty nat.

(* X0 X0 *)
Definition mymap3 := NatMap.add 0 2 (NatMap.empty nat).
Eval compute in (get_coefficient_ poly1 mymap3).

Lemma eq_all_coeff (p q : valid_pol) : p = q -> (forall (m : monoid), get_coefficient p m = get_coefficient q m).
Proof.
  unfold get_coefficient.
  destruct p,q.
  simpl.
  intro.
  eapply f_equal with (f:= fun x => VP_value x) in H.
  unfold VP_value in H.
  rewrite H. intuition.
Qed.

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

Lemma for_all_add_0_notin (m:monoid) (i:nat) :
NatMap.find i m = None -> 
P.for_all (fun _ v : nat => v =? 0) m = P.for_all (fun _ v : nat => v =? 0) (add i 0 m).
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

Lemma for_all_add_0 (m:monoid) (i:nat) : P.for_all (fun _ v : nat => v =? 0) m = true 
  -> P.for_all (fun _ v : nat => v =? 0) (add i 0 m) = true.
Proof.
  intros.
  rewrite for_all_eq_map with (m2:= add i 0 (NatMap.remove i m)).
  - erewrite <- for_all_add_0_notin.
    + apply for_all_remove; assumption.
    + rewrite F.remove_eq_o; intuition.
  - apply eq_map_add_remove.
Qed.

Lemma for_all_add_S_notin (m:monoid) (i n:nat) :
NatMap.find i m = None -> 
 P.for_all (fun _ v : nat => v =? 0) (add i (S n) m) = false.
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

Lemma coeff_n_pos (p q : poly) (i:nat) (m:monoid) : valid_b (Poly p i q) = true -> 
  (exists (n:nat), NatMap.find i m = Some (S n)) ->  
get_coefficient_ p m = 0%Z .
Proof.
  intro. 
  revert m. 
  induction p; intros.
  - simpl.
    rewrite for_all_exist_pos; [reflexivity | ].
    destruct H0.
    exists i.
    exists (S x).
    intuition.
  - simpl.
  elim (Nat.eq_dec n i); intro.
  + rewrite a in *.
    destruct q; [destruct z|]; try (andb_destr H; rewrite Nat.ltb_irrefl in H; inversion H); inversion H.
  + valid_destr H.
    specialize (IHp1 V0 m H0). 
    specialize (IHp2 V1).
    destruct (NatMap.find n m); [|apply IHp1].
    destruct n0; [apply IHp1|].
    simpl; rewrite Nat.sub_0_r.
    rewrite (IHp2 (add n n0 m)); [intuition|].
    destruct H0.
    exists x.
    rewrite F.add_neq_o; assumption.
Qed.


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

(* If [i] is (positive) in the monoid, then we can the polynom on the left if we decrement [i] in the monoid *)
Lemma coeff_remove_l (p q : poly) (i n:nat) (m:monoid) : valid_b (Poly p i q) = true -> 
  NatMap.find i m = Some (S n) ->  
  get_coefficient_ (Poly p i q) m = get_coefficient_ (q) (add i n m).
Proof.
  intros.
  simpl.
  rewrite H0.
  erewrite coeff_n_pos with (i:=i) (q:=q); [simpl; rewrite Nat.sub_0_r; reflexivity |assumption|].
  exists (n).
  assumption.
Qed.

(* If [i] is not in the monoid, then we can keep only the polynom on the right *)
Lemma coeff_remove_r (p q : poly) (i:nat) (m:monoid) : valid_b (Poly p i q) = true -> 
NatMap.find i m = None \/ NatMap.find i m = Some 0 ->  
  get_coefficient_ (Poly p i q) m = get_coefficient_ p m.
Proof.
  intros.
  simpl.
  destruct H0; rewrite H0; reflexivity.
Qed.

Lemma get_coeff_add_0_notin (p:poly) (n:nat) (m:monoid): valid_b p = true ->
NatMap.find n m = None ->
get_coefficient_ p m = get_coefficient_ p (add n 0 m).
Proof.
  intro.
  revert n.
  revert m.
  induction p; intros.
  - simpl.
    erewrite (for_all_add_0_notin m n H0); reflexivity.
  - simpl.
    valid_destr H.
    specialize (IHp1 V0 m n0 H0).
    specialize (IHp2 V1 ).
    rewrite IHp1.
    elim (Nat.eq_dec n n0); intro.
    + rewrite a in *. 
      rewrite F.add_eq_o; [|intuition].
      rewrite H0.
      reflexivity.
    + rewrite F.add_neq_o; [|intuition].
      simpl.
      destruct (NatMap.find (elt:=nat) n m); [|reflexivity].
      destruct n1; [reflexivity|].
      simpl; rewrite Nat.sub_0_r.
      rewrite get_coeff_eq_map with (m1:= add n n1 (add n0 0 m) ) (m2:= add n0 0 (add n n1 m)); [|assumption|].
      erewrite (IHp2 (add n n1 m) n0).
      * reflexivity.
      * rewrite F.add_neq_o; intuition.
      * apply eq_map_add_swap; assumption.
Qed.


Lemma get_coeff_add_same_in (p:poly) (i n:nat) (m:monoid): valid_b p = true ->
NatMap.find i m = Some n ->
get_coefficient_ p m = get_coefficient_ p (add i n m).
Proof.
  intros.
  erewrite get_coeff_eq_map with (m1:=add i n m) (m2:= m).
  intuition.
  assumption.
    rewrite <- eq_map_add_same_in; intuition.
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

Lemma coeffPosI (p q : poly) (i : nat):
   valid_b (Poly p i q) = true -> 
   exists (m : monoid), get_coefficient_ (Poly p i q) m <> 0%Z /\
   exists (n:nat), NatMap.find i m = Some (S n).
Proof.
  
  revert p i.
  induction q; intros p i V.
  - valid_destr V.
    elim (Z.eq_dec z 0); intro.
    + rewrite a in *.
      simpl in V.
      destruct p; inversion V.
    + exists (add i 1 empty_mono).
      split.
      * erewrite coeff_remove_l with (n:=0); [| assumption| rewrite F.add_eq_o; intuition].
        erewrite <- get_coeff_add_add; [|assumption].
        simpl.
        intuition.
      * exists 0. rewrite F.add_eq_o; intuition.
  - valid_destr V. apply valid_b_more in V as V1. destruct V1 as (V2 & V3).
    
      destruct IHq2 with (p := q1) (i := n). assumption.
      destruct H. destruct H0.
      
      specialize (IHq2 p i V0) as Hp1.
      destruct Hp1 as (mP1 & ?).
      destruct H1.
      destruct H2.
      
      + elim (Nat.eq_dec n i); intro.
        * rewrite a in *.
          exists (add i (S(S x0)) x).
          erewrite coeff_remove_l with (p:=p) (q:=(Poly q1 i q2)) (n:=S x0); [|assumption|].
          rewrite <- get_coeff_add_add; [|assumption].
          
          split. 
          rewrite <- get_coeff_add_same_in.
          assumption.
          assumption.
          assumption.
          exists (S  x0).
          rewrite F.add_eq_o; intuition.
          rewrite F.add_eq_o; intuition.
        * elim (option_dec (NatMap.find (elt:=nat) i x)); intro.
          -- exists (add i 1 x ).

          erewrite coeff_remove_l with (p:=p) (q:=(Poly q1 n q2)) (n:=0); [|assumption|].
          rewrite <- get_coeff_add_add; [|assumption].
          
          split. 
          rewrite <- get_coeff_add_0_notin.
          assumption.
          assumption.
          assumption.
          exists 0.
          rewrite F.add_eq_o; intuition.
          rewrite F.add_eq_o; intuition.
          -- destruct H3.
            destruct x2.
            ++ exists (add i 1 x ).
              erewrite coeff_remove_l with (p:=p) (q:=(Poly q1 n q2)) (n:=0); [|assumption|].
              rewrite <- get_coeff_add_add; [|assumption].
              split. 
              rewrite <- get_coeff_add_same_in.
              assumption.
              assumption.
              assumption.
              exists 0.
              rewrite F.add_eq_o; intuition.
              rewrite F.add_eq_o; intuition.
            
            ++ exists (add i (S (S x2)) x).
              erewrite coeff_remove_l with (p:=p) (q:=(Poly q1 n q2)) (n:=S x2); [|assumption|].
              
              split. 
              rewrite <- get_coeff_add_add.
              rewrite <- get_coeff_add_same_in.
              assumption.
              assumption.
              assumption.
              assumption.
              exists (S x2).
              rewrite F.add_eq_o; intuition.
              rewrite F.add_eq_o; intuition.
Qed.

Lemma all_coeff_dec (p1 p2 q1 q2 : poly) (i : nat) : 
  valid_b (Poly p1 i p2) = true ->
  valid_b (Poly q1 i q2) = true ->
  (forall (m : monoid), (get_coefficient_ (Poly p1 i p2) m) = (get_coefficient_ (Poly q1 i q2) m)) ->
  (forall (m : monoid), (get_coefficient_ p1 m = get_coefficient_ q1 m /\ get_coefficient_ p2 m = get_coefficient_ q2 m)).
Proof.
  intros.
  valid_destr H. valid_destr H0.
  split.
  - specialize (H1 m).
   elim (option_dec (NatMap.find i m)); intro.
    + erewrite coeff_remove_r in H1; [|assumption | left; assumption].
      erewrite coeff_remove_r in H1; [|assumption | left; assumption].
      assumption.
    + destruct H2. destruct x.
      * erewrite coeff_remove_r in H1; [|assumption | right; assumption].
      erewrite coeff_remove_r in H1; [|assumption | right; assumption].
      assumption.
      * erewrite coeff_n_pos with (i:=i) (q:=p2); [|assumption |exists x; intuition].
        erewrite coeff_n_pos with (i:=i) (q:=q2); [|assumption|exists x; intuition].
        reflexivity.
  - elim (option_dec (NatMap.find i m)); intro.
    + specialize (H1 (add i 1 m)).
      do 2 (erewrite coeff_remove_l with (n:=0) in H1; [|assumption |rewrite F.add_eq_o; intuition ]).
      do 2 (rewrite <- get_coeff_add_add in H1; [|assumption]).
      do 2 (rewrite <- get_coeff_add_0_notin in H1; [|assumption|assumption]).
      assumption.
    + destruct H2. destruct x.
      * specialize (H1 (add i 1 m)).
      do 2 (erewrite coeff_remove_l with (n:=0) in H1; [|assumption |rewrite F.add_eq_o; intuition ]).
      do 2 (rewrite <- get_coeff_add_add in H1; [|assumption]).
      do 2 (rewrite <- get_coeff_add_same_in in H1; [|assumption|assumption]).
      assumption.
      * specialize (H1 (add i (S (S x)) m)).
        do 2 (erewrite coeff_remove_l with (n:=S x) in H1; [|assumption |rewrite F.add_eq_o; intuition ]).
        do 2 (rewrite <- get_coeff_add_add in H1; [|assumption]).
        do 2 (rewrite <- get_coeff_add_same_in in H1; [|assumption|assumption]).
        assumption.
Qed.
 


Lemma all_coeff_eq (p q : valid_pol) : (forall (m : monoid), get_coefficient p m = get_coefficient q m) -> p = q.
Proof.
  unfold get_coefficient.
  destruct p as [p propP]. 
  destruct q as [q propQ].
  simpl.
  intro.
  apply leibniz.
  simpl.

  revert q H propQ propP.
  
  induction p.

  -  induction q. 
    + intros. specialize (H empty_mono). simpl in H. f_equal. assumption.
    + intros. 
      valid_destr propQ.
      apply coeffPosI in propQ.
      destruct propQ.
      specialize (H x).
      destruct H0.
      rewrite <- H in H0.
      simpl in H0.
      destruct H1.
      rewrite for_all_exist_pos in H0; [| exists n; exists (S x0); intuition].
      specialize (H0 eq_refl); contradiction.  

  - induction q.
    + intros.
    valid_destr propP.
    eapply coeffPosI in propP.
    destruct propP.
    specialize (H x).
    destruct H0.
    rewrite H in H0.
    simpl in H0.
    destruct H1.
    rewrite for_all_exist_pos in H0; [|  exists n; exists (S x0); rewrite H1; intuition].
    specialize (H0 eq_refl); contradiction.  

    + intros.
      valid_destr propQ. valid_destr propP. 
      specialize propQ as propQ'.  specialize propP as propP'.
      elim (Nat.eq_dec n0 n); intro.
      * rewrite a in *. apply f_equal3 with (f:=Poly); [|intuition|].
        -- apply (IHp1 q1); [|assumption|assumption].
          eapply all_coeff_dec with (p2:=p3) (i:=n) (q2:=q2) ; assumption.
        -- apply (IHp2 q2); [|assumption|assumption].
        eapply all_coeff_dec with (p1:=p2) (p2:=p3) (i:=n) (q1:=q1) (q2:=q2); assumption .
      * 
        apply coeffPosI in propP.
        apply coeffPosI in propQ.
        destruct propP as (mP & ?).  destruct propQ as (mQ & ?).

        specialize (H mP) as HmP.
        specialize (H mQ) as HmQ.
        destruct H0.  destruct H1.
        destruct H3. destruct H2.
        
        elim (gt_eq_gt_dec n n0); intro.
        -- elim a; intro.
          ++ eapply le_valid with (i:=n0) (p:=q1) (q:=q2) in propP'; [|assumption|assumption].
            
            erewrite coeff_n_pos with (p:=(Poly q1 n0 q2)) (i:=n) (q:=p3) in HmP; [|assumption|exists x0; intuition ].

            rewrite HmP in H0.
            specialize (H0 eq_refl); contradiction.
          ++ rewrite b0 in b. specialize (b eq_refl); contradiction.
          
        -- eapply le_valid with (i:=n) (p:=p2) (q:=p3) (q':=q2) in propQ'; [|assumption|assumption].
          erewrite coeff_n_pos with (p:=(Poly p2 n p3)) (i:=n0) (q:=q2) in HmQ; [ |assumption | exists x; assumption ].
          rewrite <- HmQ in H1.
          specialize (H1 eq_refl); contradiction.
Qed.


Fixpoint poly_val_ (pol:poly) (f : nat -> Z) := 
  match pol with 
  | Cst z => z
  | Poly p i q => 
    Z.add (poly_val_ p f) (Z.mul (f i) (poly_val_ q f))
end.

Definition poly_val (pol:valid_pol) (f : nat -> Z) := 
 poly_val_ (VP_value pol) f 
.



Lemma val_coeff (p q : valid_pol) : (forall (f:nat -> Z), poly_val p f = poly_val q f) -> (forall (m: monoid ), get_coefficient p m = get_coefficient q m).
Proof.
  intros.
  destruct p as [p ].
  destruct q as [q ].
  
  unfold get_coefficient.
  unfold VP_value.
  unfold poly_val in H.
  unfold VP_value in H.
  revert m  p VP_prop0 H .

  induction q.
  - intro. 
    + intros. 
      simpl in H.

      elim (Z.eq_dec (poly_val_ p (fun _ => 0%Z)) z); intro.
      * 
        induction p.
        -- specialize (H (fun _ => 0%Z)).
          simpl in H. 
          rewrite H.
          reflexivity.
        -- simpl in H. 
Admitted.


Section BTauto.

Definition impb (b1 b2: bool) := if b1 then b2 else true.


Inductive form : Set :=
| f_true 	: form 
| f_false   : form 
| f_var 	: nat -> form 
| f_and 	: form -> form -> form 
| f_or  	: form -> form -> form
| f_not 	: form -> form
(* | f_imp 	: form -> form -> form *)
.
Fixpoint eval_form (f:form) (val : nat -> bool) : bool := 
  match f with 
  | f_true => true
  | f_false => false
  | f_var i => val i
  | f_and f1 f2 => eval_form f1 val && eval_form f2 val
  | f_or f1 f2 => eval_form f1 val || eval_form f2 val
  | f_not f1 => negb (eval_form f1 val	)
  (* | f_imp f1 f2 => impb (eval_form f1 val) (eval_form f2 val) *)
  end.  


Hint Constructors form : core.
Notation "A ∧ B" := (f_and A B) (at level 30, right associativity).
Notation "A ∨ B" := (f_or A B) (at level 35, right associativity).
(* Notation "A → B" := (f_imp A B) (at level 49, right associativity, B at level 50). *)
Notation "⊤" := (f_true) (at level 5).
Notation "⊥" := (f_false) (at level 5).
Notation "# x" := (f_var x) (at level 10).
Notation "! A" := (f_not A) (at level 11).


Definition valuation := (fun x => match x with |0 => false |_=> true end).

Eval compute in (eval_form (# 0 ∨ # 1) valuation).
(* Eval compute in (eval_form (# 0 → # 1) valuation).
Eval compute in (eval_form (# 1 → # 0) valuation).
Eval compute in (eval_form (# 1 → # 1) valuation). *)


From Coq Require Import List .
Import ListNotations .

Ltac list_add a l :=
  let rec aux a l n :=
    match l with
    | [] => constr :(( n , a :: l ))
    | a :: _ => constr :(( n , l ))
    | ?x :: ?l =>
      match aux a l ( S n ) with
      | (?n , ?l ) => constr :(( n , x :: l ))
      end
  end in
  aux a l O .

Ltac read_term f l :=
match f with
|negb ?x => 
  match read_term x l with
  |(?x' , ?l') => constr:(( f_not x' , l'))
  end
|andb ?x ?y =>
  match read_term x l with
  |(?x' , ?l') => match read_term y l' with
    |(?y' , ?l'') => constr:(( f_and x' y' , l''))
  end end
|orb ?x ?y =>
  match read_term x l with
  |(?x' , ?l') => match read_term y l' with
    |(?y' , ?l'') => constr:(( f_or x' y' , l''))
  end end
(* |impb ?x ?y => 
  match read_term x l with
  |(?x' , ?l') => match read_term y l' with
    |(?y' , ?l'') => constr:(( f_imp x' y' , l''))
  end end *)
|false => constr:((f_false , l))
|true => constr:((f_true , l))

|_ => 
  match list_add f l with
  | (?n , ?l') =>  constr:(( f_var n , l'))
  end
end.


Goal forall b : bool , True .
intros b.
let v := read_term (andb b ( negb b)) (@nil bool) in
idtac v.
let v := read_term (orb b (negb ( negb b))) (@nil bool) in
idtac v.
let v := read_term (andb b (negb false)) (@nil bool) in
idtac v.
let v := read_term (orb (negb false) true) (@nil bool) in
idtac v.
let v := read_term (impb (negb b) true) (@nil bool) in
idtac v.
Abort .


Definition cst_poly (z:Z) := {| VP_value := (Cst z); VP_prop := eq_refl |}.

From Equations Require Import Equations.

Fixpoint length (p:poly) := 
  match p with 
  |Cst _ => 1 
  |Poly p _ q => S ((length p) + (length q))
  end.

Obligation Tactic := try (unfold Nat.max; simpl; intuition).

Equations sum_poly_ (p q:poly) : poly by wf (length p + length q) :=
  sum_poly_ (Cst z1) (Cst z2) := Cst (Z.add z1 z2) ;
  sum_poly_ (Poly p1 i q1) (Cst z2) := Poly (sum_poly_ p1 (Cst z2) ) i q1;
  sum_poly_ (Cst z1) (Poly p2 j q2) := Poly (sum_poly_ (Cst z1) p2 ) j q2 ;
  (* when the sum of 2 constants on the right is zero, we just keep the left part *)
  (* sum_poly_ (Poly p1 i (Cst z1)) (Poly p2 i (Cst z2)) := 
    if Z.eqb (Z.add z1 z2) 0%Z then sum_poly_ p1 p2 
    else Poly (sum_poly_ p1 p2) i (Cst (Z.add z1 z2)); *)
  sum_poly_ (Poly p1 i q1) (Poly p2 j q2) := 
    match Nat.compare i j with
    | Eq => Poly (sum_poly_ p1 p2) i (sum_poly_ q1 q2)
    | Lt => Poly (sum_poly_ p1 (Poly p2 j q2)) i q1
    | Gt => Poly (sum_poly_ p2 (Poly p1 i q1)) j q2
    end
. 


Fixpoint weak_valid_b (pol:poly) : bool := 
  match pol with
  |Cst _ => true
  |Poly p i q => 
    match p,q with 
    | (Cst _), (Cst _) => true 
    | (Poly _ j1 _), (Cst _) => Nat.ltb i j1 && weak_valid_b p 
    | (Cst _),  (Poly p2 j2 q2) => Nat.leb i j2 && weak_valid_b q 
    |(Poly p1 j1 q1),  (Poly p2 j2 q2) => 
      Nat.ltb i j1 && Nat.leb i j2 
      && weak_valid_b p 
      && weak_valid_b q
    end 
  end
.

Fixpoint remove_null_r (pol:poly) : poly :=
  match pol with 
  |Cst z => Cst z
  |Poly p i (Cst 0%Z) => remove_null_r p 
  |Poly p i q => Poly (remove_null_r p) i (remove_null_r q) 
  end.

Goal sum_poly_ (Poly (Cst 1%Z) 1 (Poly (Cst 1%Z) 2 (Cst (-1%Z)))) (Poly (Cst 1%Z) 1 (Poly (Cst 1%Z) 2 (Cst 1%Z))) = (Cst 0%Z).
simp sum_poly_. simpl.
Abort.

Lemma sum_pol_sym (p q:poly) : 
valid_b p = true -> 
valid_b q = true -> 
sum_poly_ p q = sum_poly_ q p.
Proof.
  revert q.
  induction p; intros.
  - induction q. 
    + simp sum_poly_.  apply f_equal. intuition.
    + simp sum_poly_. valid_destr H0. rewrite (IHq1 V0). apply f_equal. reflexivity.
  
  - valid_destr H.
    specialize (IHp1 q V0 H0) as HQ1. 
    specialize (IHp2 q V1 H0) as HQ2.
    destruct q.
    + simp sum_poly_. rewrite HQ1. apply f_equal. reflexivity.
    + simp sum_poly_.
      elim (gt_eq_gt_dec n n0); intro.
      * elim a; intro.
        -- eapply nat_compare_gt in a0 as a_gt.  
          eapply nat_compare_lt in a0 as a_lt.  
          rewrite a_gt. 
          rewrite a_lt.
          rewrite HQ1. apply f_equal. reflexivity.
        -- rewrite b in *.
          rewrite Nat.compare_refl.
          valid_destr H0.
          rewrite (IHp1 q1 V0 V2).
          rewrite (IHp2 q2 V1 V3).
          apply f_equal. reflexivity.
      * eapply nat_compare_gt in b as a_gt.  
        eapply nat_compare_lt in b as a_lt.  
        rewrite a_gt. 
        rewrite a_lt.
        apply f_equal. reflexivity.
Qed.


Lemma valid_sum_cst_p (p q:poly) (i:nat) (z:Z) : 
valid_b (Poly p i q) = true -> 
valid_b (sum_poly_ (Cst z) p) = true ->
valid_b (Poly (sum_poly_ (Cst z) p) i q) = true.
Proof.
  revert z i p q .
  induction p.
  - intros.
    simp sum_poly_.
    

  - intros. simp sum_poly_.
    valid_destr H.
    specialize (IHp1 q V0).
    simp sum_poly_ in H0.
    valid_destr H0.
    specialize (IHp1 V2).
      eapply le_valid  with (i:=n) (p':=p2).
      + eapply valid_le in H. assumption.
      + assumption.
      + assumption.
Qed. 


Lemma valid_sum_le (p1 p2 q1 q2:poly) (i j:nat) : valid_b (Poly (sum_poly_ q1 (Poly p1 i p2)) j q2) = true -> j < i.
Proof.
  intro.
  induction q1.
  - simp sum_poly_ in H. eapply valid_le in H. assumption.
  - simp sum_poly_ in H.
    elim (gt_eq_gt_dec n i); intro.
      * elim a; intro.
      -- eapply nat_compare_lt in a0 as a1.
        rewrite a1 in *.
        valid_destr H.
        specialize (IHq1_1 V0).
        assumption.
      -- rewrite b in *.
        rewrite Nat.compare_refl in H.
        valid_destr H.
        apply valid_le in H.
        assumption.
      * eapply nat_compare_gt in b as a.
        rewrite a in H.
        apply valid_le in H.
        assumption.
Qed.

Lemma weaken_valid (p:poly) (H:valid_b p = true) : weak_valid_b p = true.
Proof.
  induction p.
  - simpl. reflexivity.
  - valid_destr H.
    specialize (IHp1 V0).
    specialize (IHp2 V1).
    simpl in *.
    destruct p2.
    * destruct p3.
      destruct z0; reflexivity.
      andb_split. andb_destr H. assumption.
      assumption.
    * destruct p3.
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

Lemma weak_sum_pol_sym (p q:poly) : 
weak_valid_b p = true -> 
weak_valid_b q = true -> 
sum_poly_ p q = sum_poly_ q p.
Proof.
  revert q.
  induction p; intros.
  - induction q. 
    + simp sum_poly_.  apply f_equal. intuition.
    + simp sum_poly_. apply weak_valid_b_more in H0 as (V0 & V1). rewrite (IHq1 V0). apply f_equal. reflexivity.
  
  - apply weak_valid_b_more in H as (V0 & V1).
    specialize (IHp1 q V0 H0) as HQ1. 
    specialize (IHp2 q V1 H0) as HQ2.
    destruct q.
    + simp sum_poly_. rewrite HQ1. apply f_equal. reflexivity.
    + simp sum_poly_.
      elim (gt_eq_gt_dec n n0); intro.
      * elim a; intro.
        -- eapply nat_compare_gt in a0 as a_gt.  
          eapply nat_compare_lt in a0 as a_lt.  
          rewrite a_gt. 
          rewrite a_lt.
          rewrite HQ1. apply f_equal. reflexivity.
        -- rewrite b in *.
          rewrite Nat.compare_refl.
          apply weak_valid_b_more in H0 as (V2 & V3).
          rewrite (IHp1 q1 V0 V2).
          rewrite (IHp2 q2 V1 V3).
          apply f_equal. reflexivity.
      * eapply nat_compare_gt in b as a_gt.  
        eapply nat_compare_lt in b as a_lt.  
        rewrite a_gt. 
        rewrite a_lt.
        apply f_equal. reflexivity.
Qed.

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

Lemma weak_valid_sum_cst_p (p q:poly) (i:nat) (z:Z) : 
weak_valid_b (Poly p i q) = true -> 
weak_valid_b (sum_poly_ (Cst z) p) = true ->
weak_valid_b (Poly (sum_poly_ (Cst z) p) i q) = true.
Proof.
  revert z i p q .
  induction p.
  - intros.
    simp sum_poly_.
    

  - intros. simp sum_poly_.
    
    specialize H as V. apply weak_valid_b_more_l in V as (V0 & V1).
    specialize (IHp1 q V0).
    simp sum_poly_ in H0.
    specialize H0 as V. apply weak_valid_b_more in V as (V2 & V3).
    specialize (IHp1 V2).
      eapply le_weak_valid  with (i:=n) (p':=p2).
      + eapply weak_valid_le in H. assumption.
      + assumption.
      + assumption.
Qed. 

Lemma lt_inv_le (n n0 : nat) : (n0 ?= n) = Lt -> (n ?= n0) = Gt.
Proof.
  
  - intro. 
    elim (gt_eq_gt_dec n0 n); intro.
    + elim a; intro.
      * eapply nat_compare_gt in a0 as a1. rewrite a1. trivial.
      * rewrite b in *. rewrite Nat.compare_refl in H. inversion H.
    + eapply nat_compare_gt in b as b1. 
      rewrite b1 in H. inversion H.
Qed.

Lemma weak_val_eq  (p2 p3 q1 q2 : poly) (n0 n1 : nat) :  
(forall q : poly, weak_valid_b q = true -> weak_valid_b (sum_poly_ p2 q) = true) ->
(forall q : poly, weak_valid_b q = true -> weak_valid_b (sum_poly_ p3 q) = true) -> 
weak_valid_b (Poly p2 n0 p3) = true ->
weak_valid_b (Poly q1 n0 q2) = true -> 
weak_valid_b (sum_poly_ (Poly p2 n0 p3) q1) = true ->
weak_valid_b (sum_poly_ (Poly p2 n0 p3) q2) = true ->
weak_valid_b (Poly (sum_poly_ p2 q1) n0 (sum_poly_ p3 q2)) = true
.
Proof.
  intro. intro.
  intros.
  induction q1. 
  - destruct p2.
    + simp sum_poly_. 
      simpl.
      destruct p3.
      * destruct q2.
        -- simp sum_poly_.
        -- simp sum_poly_.
          andb_split.
          apply weak_valid_leq in H2. auto.
           apply weak_valid_b_more in H2. destruct H2. 
          specialize (H0 (Poly q2_1 n q2_2) H5).
          simp sum_poly_ in H0.
      * destruct q2.
        -- simp sum_poly_.
          andb_split.
          apply weak_valid_leq in H1. auto.
          apply weak_valid_b_more in H2. destruct H2. 
          specialize (H0 (Cst z1) H5).  
          simp sum_poly_ in H0.
        -- simp sum_poly_. simp sum_poly_ in H3.  
          elim (gt_eq_gt_dec n2 n); intro.
          ++ elim a; intro.
            ** eapply nat_compare_gt in a0 as a1. rewrite a1.
              andb_split.
              apply weak_valid_leq in H2. auto.
              apply weak_valid_b_more in H2. destruct H2. 
              specialize (H0 (Poly q2_1 n2 q2_2) H5). simp sum_poly_ in H0. rewrite a1 in H0. assumption.
            ** rewrite b in *. rewrite Nat.compare_refl. andb_split.
              apply weak_valid_leq in H3. auto.
              apply weak_valid_b_more in H2. destruct H2.
              specialize (H0 (Poly q2_1 n q2_2) H5). simp sum_poly_ in H0. rewrite Nat.compare_refl in H0. assumption.
          ++ eapply nat_compare_lt in b as b1. rewrite b1. andb_split.
            apply weak_valid_leq in H1. auto.
            apply weak_valid_b_more in H2. destruct H2. 
            specialize (H0 (Poly q2_1 n2 q2_2) H5). simp sum_poly_ in H0. rewrite b1 in H0. assumption.
    + simp sum_poly_. 
      apply weak_valid_le in H1 as Hlt.
      apply nat_compare_lt in Hlt as Hlt2.
      specialize (H (Poly (Cst z) n0 (sum_poly_ p3 q2)) ) as HN2.
      simp sum_poly_ in HN2.
      
      
      destruct p3.
      * simp sum_poly_ in H3.
        destruct q2. 
        simp sum_poly_.    
        simp sum_poly_. simp sum_poly_ in H0. simp sum_poly_ in H.

        apply lt_inv_le in Hlt2 as Htl3. rewrite Htl3 in HN2. simp sum_poly_ in HN2.
        rewrite weak_sum_pol_sym. 
        apply HN2.
        apply weak_valid_b_more in H1 as HH. destruct HH.
Abort.

Lemma sum_weak_valid_lt (p2 p3 q1 q2 : poly) (n n0:nat) : 
n < n0 -> 
weak_valid_b (Poly p2 n p3) = true ->
weak_valid_b (Poly q1 n0 q2) = true ->
weak_valid_b (sum_poly_ (Poly p2 n p3) q1) = true ->
weak_valid_b (sum_poly_ (Poly p2 n p3) q2) = true ->
weak_valid_b (Poly (Poly q1 n0 q2) n p3) = true -> 
weak_valid_b (sum_poly_ p2 (Poly q1 n0 q2)) = true ->
weak_valid_b (Poly (sum_poly_ p2 (Poly q1 n0 q2)) n p3) = true
.
Proof.
  intros.
  destruct p2.
  ++ simp sum_poly_. simp sum_poly_ in *.
    destruct p3.
    ** andb_split; auto.
    ** simpl in H4. andb_destr H4. andb_split; try assumption.
    ++ simp sum_poly_. 
    elim (gt_eq_gt_dec n1 n0); intro.
    ** elim a; intro.
      --- eapply nat_compare_lt in a0 as a1.
        simp sum_poly_ in H5. rewrite a1 in *.
        apply weak_valid_le in H0 as VP1.
        eapply le_weak_valid; intuition.
      --- rewrite b in *.
          simp sum_poly_ in H5.
          rewrite Nat.compare_refl in *.
          eapply le_weak_valid; intuition.
    ** eapply nat_compare_gt in b as b1.
        simp sum_poly_ in H5.
        rewrite b1 in *.
        eapply le_weak_valid; intuition.
Qed.

Lemma weak_sum_leq (p1 p2 q1 q2:poly) (n0:nat): 
weak_valid_b (Poly p1 n0 p2) = true ->
weak_valid_b (Poly q1 n0 q2) = true -> 
match sum_poly_ p2 q2 with 
|Cst _ => true 
|Poly _ j _ => n0 <=? j 
end = true
.
Proof.
  induction p2; induction q2; intros; simp sum_poly_.
  -  trivial.
  - apply weak_valid_leq in H0. auto.
  - apply weak_valid_leq in H. auto.
  - apply weak_valid_leq in H. apply weak_valid_leq in H0.  destruct (n ?= n1).
    + auto.
    + auto.
    + auto.
Qed.

Lemma weak_sum_gt (p1 p2 q1 q2:poly) (n0:nat): 
weak_valid_b (Poly p1 n0 p2) = true ->
weak_valid_b (Poly q1 n0 q2) = true -> 
match sum_poly_ p1 q1 with 
|Cst _ => true 
|Poly _ j _ => n0 <? j 
end = true
.
Proof.
  induction p1; induction q1; intros; simp sum_poly_.
  -  trivial.
  - apply weak_valid_le in H0. auto.
  - apply weak_valid_le in H. auto.
  - apply weak_valid_le in H. apply weak_valid_le in H0.  destruct (n ?= n1).
    + auto.
    + auto.
    + auto.
Qed.


Lemma sum_weak_valid (p q:poly) : weak_valid_b p = true -> weak_valid_b q = true -> weak_valid_b (sum_poly_ p q) = true.
Proof.
  intros VP VQ.
  revert p VP q VQ.
  induction p.
  - induction q; intro.
    + simp sum_poly_.
    + specialize VQ as V. apply weak_valid_b_more in V; destruct V as (V0 & V1).
      specialize (IHq1 V0).
      specialize (IHq2 V1).
      simp sum_poly_.
      eapply weak_valid_sum_cst_p; assumption.
  - intros.
    specialize VP as V. apply weak_valid_b_more in V as (V0 & V1).
    specialize (IHp1 V0 ).
    specialize (IHp2 V1 ).
    induction q.
    + simp sum_poly_.
      rewrite weak_sum_pol_sym; try assumption.
      eapply weak_valid_sum_cst_p.
      assumption.
      specialize (IHp1 (Cst z) VQ). rewrite weak_sum_pol_sym; assumption.
    + specialize VQ as V. apply weak_valid_b_more in V as (V2 & V3).
      specialize (IHq1 V2). specialize (IHq2 V3).
      simp sum_poly_.
      elim (gt_eq_gt_dec n n0); intro.
      * elim a; intro.
        -- eapply nat_compare_lt in a0 as a1.
          
          rewrite a1.
          eapply le_weak_valid with (p:=q1) (q:=q2) (p':=p2) (q':=p3) in a0 as a2; try assumption.
          specialize (IHp1 (Poly q1 n0 q2) VQ) as HN1.
          eapply sum_weak_valid_lt; intuition.

        -- rewrite b in *. rewrite Nat.compare_refl.
          specialize (IHp1 (Poly q1 n0 q2) VQ) as HN1.
          specialize (IHp2 (Poly q1 n0 q2) VQ) as HN2.
          simpl. 

          destruct p2.
          ++ destruct q1.
            ** simp sum_poly_.
              apply weak_valid_b_more in VQ. destruct VQ. specialize (IHp2 q2 H0) as HN3.
              destruct p3.
              destruct q2. simp sum_poly_.
              simp sum_poly_ in HN3. simp sum_poly_ in HN2. apply weak_valid_leq in HN2. andb_split; intuition.
              destruct q2. simp sum_poly_.
              simp sum_poly_. apply weak_valid_leq in VP. simp sum_poly_ in HN3. andb_split; intuition.
              simp sum_poly_ in HN1. simp sum_poly_. simp sum_poly_ in HN3. apply weak_valid_leq in VP. apply weak_valid_leq in HN1. 
              destruct (n1 ?= n2).
              andb_split; intuition.
              andb_split; intuition.
              andb_split; intuition.

            ** simp sum_poly_. 
              destruct p3.
              --- destruct q2. simp sum_poly_. simp sum_poly_ in HN1.
                simp sum_poly_ in HN1. simp sum_poly_ in HN2.
                simp sum_poly_.
                andb_split.
                apply weak_valid_le in HN1. intuition.
                apply weak_valid_leq in HN1. intuition.
                apply weak_valid_b_more in HN1; destruct HN1. assumption.
                
                simpl.
                destruct q2_1.
                simp sum_poly_.
                simp sum_poly_.
                destruct q2_2.
                +++ andb_split.
                  apply weak_valid_b_more in HN2; destruct HN2. apply weak_valid_le in H0. auto.
                  apply weak_valid_b_more in VQ as VQ0. destruct VQ0. apply weak_valid_b_more in H0 as VQ1. destruct VQ1. 
                  specialize (IHp2 (Poly q2_1_1 n3 q2_1_2) H1).
                  simp sum_poly_ in IHp2.
                +++ andb_split.
                  apply weak_valid_b_more in HN2; destruct HN2. apply weak_valid_le in H0. auto.
                  apply weak_valid_b_more in HN2; destruct HN2. apply weak_valid_leq in H0. auto.
                  apply weak_valid_b_more in VQ as VQ0. destruct VQ0. apply weak_valid_b_more in H0 as VQ1. destruct VQ1.  
                  specialize (IHp2 (Poly q2_1_1 n3 q2_1_2) H1).
                  simp sum_poly_ in IHp2.
                  apply weak_valid_b_more in VQ; destruct VQ. apply weak_valid_b_more in H0; destruct H0.
                  assumption.
              --- destruct q2. simp sum_poly_. simp sum_poly_ in HN1. simp sum_poly_ in IHq2.
                  andb_split.
                  apply weak_valid_le in HN1. intuition.
                  apply weak_valid_leq in IHq2. intuition. 
                  apply weak_valid_b_more in VQ as (H & ?). specialize (IHp1 (Poly q1_1 n1 q1_2) H).  simp sum_poly_ in IHp1. 
                  specialize (IHp2 (Cst z0) V3). simp sum_poly_ in IHp2. 
                
                  simp sum_poly_.

                  simp sum_poly_ in HN1. 
                  apply weak_valid_leq in VP as HPleq. apply Nat.compare_le_iff in HPleq as HPleq'.
                  apply weak_valid_leq in VQ as HQleq. apply Nat.compare_le_iff in HQleq as HQleq'.
                  apply weak_valid_le in VQ as HQlt. apply nat_compare_lt in HQlt as HQlt'.
                  

                  elim (gt_eq_gt_dec n3 n2); intro.
                  +++ elim a0; intro.
                    *** apply nat_compare_gt in a1 as a2.
                      rewrite a2.
                      andb_split.
                        
                      simp sum_poly_ in IHq1. rewrite HQlt' in IHq1. 
                      auto.
                      auto.
                      specialize (IHp1 (Poly q1_1 n1 q1_2) V2). simp sum_poly_ in IHp1.
                      specialize (IHp2 (Poly q2_1 n3 q2_2) V3). simp sum_poly_ in IHp2. rewrite a2 in IHp2. assumption.
                    *** rewrite b0 in *. rewrite Nat.compare_refl. andb_split.
                      auto. auto.
                      apply weak_valid_b_more in HN1. destruct HN1. assumption.
                      specialize (IHp2 (Poly q2_1 n2 q2_2) V3). simp sum_poly_ in IHp2. rewrite Nat.compare_refl in IHp2. assumption.
                  +++ simp sum_poly_ in IHq1.
                    rewrite HQlt' in IHq1.
                    apply nat_compare_lt in b0 as b1.
                    rewrite b1.
                    andb_split.
                    auto. auto.
                    apply weak_valid_b_more in IHq1. destruct IHq1. assumption.
                    specialize (IHp2 (Poly q2_1 n3 q2_2) V3). simp sum_poly_ in IHp2. rewrite b1 in IHp2. assumption.

          ++ simp sum_poly_ in HN1. 
            apply weak_valid_le in VP as Hlt.
            eapply nat_compare_gt in Hlt.
            rewrite Hlt in HN1. simpl in HN1. rewrite weak_sum_pol_sym; try assumption.
            destruct (sum_poly_ q1 (Poly p2_1 n1 p2_2)).
            destruct q2. destruct p3.
            simp sum_poly_.
            simp sum_poly_.
            apply weak_valid_leq in VP as Hleq. andb_split. auto.
            specialize (IHp2 (Cst z0) V3). simp sum_poly_ in IHp2.
            assert (aaaa : match sum_poly_ p3 (Poly q2_1 n2 q2_2) with
            | Cst _ => true
            | Poly _ j _ => n0 <=? j
            end = true).
                        eapply weak_sum_leq with (p1:=(Poly p2_1 n1 p2_2)) (q1:=q1). assumption. assumption.
                        specialize (IHp2 (Poly q2_1 n2 q2_2) V3). 
                        destruct (sum_poly_ p3 (Poly q2_1 n2 q2_2)).
                        trivial.
                        andb_split. assumption. assumption.
            assert (aaaa : match sum_poly_ p3 q2 with
            | Cst _ => true
            | Poly _ j _ => n0 <=? j
            end = true).
            eapply weak_sum_leq with (p1:=(Poly p2_1 n1 p2_2)) (q1:=q1). assumption. assumption.

            destruct q2.
            specialize (IHp2 (Cst z) V3).
            destruct (sum_poly_ p3 (Cst z)). andb_destr HN1.
            andb_split. auto. assumption.
            andb_destr HN1. andb_split. auto. auto. assumption. assumption.
            specialize (IHp2 (Poly q2_1 n3 q2_2) V3).
            destruct (sum_poly_ p3 (Poly q2_1 n3 q2_2)). andb_destr HN1.
            andb_split. auto. assumption.
            andb_destr HN1. andb_split. auto. auto. assumption. assumption.
    * apply nat_compare_gt in b as b1.
      rewrite b1.
      simpl.
      destruct q1.
      -- simp sum_poly_.
        destruct q2. andb_split. auto. simp sum_poly_ in IHq1. rewrite weak_sum_pol_sym; assumption.
        andb_split. auto. eapply weak_valid_leq in VQ. auto. 
        simp sum_poly_ in IHq1.   rewrite weak_sum_pol_sym; assumption.
        assumption.
      -- 
          assert (aaa : match sum_poly_ (Poly q1_1 n1 q1_2) (Poly p2 n p3) with
        | Cst _ => true
        | Poly _ j1 _ => (n0 <? j1) 
        end = true).
        rewrite weak_sum_pol_sym; try assumption.
        simp sum_poly_ in IHq1.
        simp sum_poly_.
        destruct (n ?= n1).
        ++ auto.
        ++ auto.
        ++ apply weak_valid_le in VQ. auto.
        ++ rewrite weak_sum_pol_sym in IHq1; try assumption. 
          destruct q2.
          ** destruct (sum_poly_ (Poly q1_1 n1 q1_2) (Poly p2 n p3)). 
            trivial.
            andb_split. auto. assumption.
          **  destruct (sum_poly_ (Poly q1_1 n1 q1_2) (Poly p2 n p3)).
            --- andb_split. apply weak_valid_leq in VQ. auto. assumption.
            --- andb_split. auto.  apply weak_valid_leq in VQ. auto.  assumption. assumption.
          
Qed.

Lemma sum_valid (p q:poly) : valid_b p = true -> valid_b q = true -> valid_b (remove_null_r (sum_poly_ p q)) = true.
Proof.
  intros VP VQ.
  revert p VP q VQ.
  induction p.
  - induction q; intro.
    + simp sum_poly_.
    + simp sum_poly_.
      valid_destr VQ.
      specialize (IHq1 V0).
      specialize (IHq2 V1).
      induction q2.
      * simpl.
Abort.


Program Definition sum_poly (p q:valid_pol) := {|VP_value := remove_null_r (sum_poly_ (VP_value p) (VP_value q)) ; VP_prop := _ |}.
(* Next Obligation.
  destruct p as [p VP].
  destruct q as [q VQ].
  unfold VP_value.
  revert q VQ p VP.
  induction q.
  - induction p.
    + simp sum_poly_.
    + intros.
      valid_destr VP.
      specialize (IHp1 V0 ) as Hp1.
      specialize (IHp2 V1 ) as Hp2.
      simp sum_poly_.
      rewrite sum_pol_sym; try assumption.
      eapply valid_sum_cst_p; try assumption.
      rewrite sum_pol_sym; assumption.

  - intros VQ p VP.
    valid_destr VQ.
    specialize (IHq1 V0).
    specialize (IHq2 V1).

    induction p; intros.
    + simp sum_poly_.
      eapply valid_sum_cst_p.
      assumption.
      rewrite sum_pol_sym.
      specialize (IHq1 (Cst z) VP). rewrite sum_pol_sym; assumption.
      assumption.
      assumption.
    + valid_destr VP.
      specialize (IHp1 V2).
      specialize (IHp2 V3).
      simp sum_poly_. 
      elim (gt_eq_gt_dec n n0); intro.
      * elim a; intro.
        -- eapply nat_compare_gt in a0 as a1.
          rewrite a1.
          specialize (IHq1 (Poly p2 n0 p3) VP) as HN1.
          rewrite sum_pol_sym; try assumption.
          simpl.
          admit.
        -- rewrite <- b in *. rewrite Nat.compare_refl.
        
Admitted. *)
Admit Obligations.


Equations mul_poly_ (p q:poly) : poly by wf (length p + length q) :=
  mul_poly_ (Cst z1) (Cst z2) := Cst (z1 * z2);
  mul_poly_ (Poly p1 i q1) (Cst z2) := Poly (mul_poly_ p1 (Cst z2)) i (mul_poly_ q1 (Cst z2));
  mul_poly_ (Cst z1) (Poly p2 j q2) := Poly (mul_poly_ p2 (Cst z1)) j (mul_poly_ q2 (Cst z1));
  mul_poly_ (Poly p1 i q1) (Poly p2 j q2) :=
    match Nat.compare i j with
    |Eq => sum_poly_ (Poly (mul_poly_ p1 p2) i (Poly (mul_poly_ p2 q1) j (mul_poly_ q1 q2))) (Poly (Cst 0) i (mul_poly_ p1 q2)) 
    |Lt => Poly (mul_poly_ p1 (Poly p2 j q2)) i (mul_poly_ q1 (Poly p2 j q2))
    |Gt => Poly (mul_poly_ p2 (Poly p1 i q1)) j (mul_poly_ q2 (Poly p1 i q1))
    end
.

Goal mul_poly_ (Poly (Cst 3) 0 (Cst 1)) (Poly (Cst (-2%Z)) 0 (Cst 2)) = Poly (Cst (-6)) 0 (Poly (Cst 4) 0 (Cst 2)).
  simp mul_poly_. simpl.
  simp sum_poly_. simpl.
Abort.

Goal mul_poly_ (Poly (Cst (-2%Z)) 0 (Cst 2)) (Poly (Cst 3) 0 (Cst 1)) = Poly (Cst (-6)) 0 (Poly (Cst 4) 0 (Cst 2)).
  simp mul_poly_. simpl.
  simp sum_poly_. simpl.
Abort.

Lemma mul_poly_sym (p q :poly) : mul_poly_ p q = mul_poly_ q p.
Proof.
  revert p q.
  induction p; intros.
  - destruct q.
    + simp mul_poly_. apply f_equal. intuition.
    + simp mul_poly_. apply f_equal. reflexivity.
  - destruct q.
    + simp mul_poly_. apply f_equal. intuition.
    + simp mul_poly_. 
    elim (gt_eq_gt_dec n n0); intro.
      * elim a; intro.
        -- eapply nat_compare_gt in a0 as a_gt.  
          eapply nat_compare_lt in a0 as a_lt.  
          rewrite a_gt. 
          rewrite a_lt.
          reflexivity.
        -- rewrite b in *.
          simp sum_poly_.  
          rewrite Nat.compare_refl.
          rewrite (IHp1 q1).
          rewrite (IHp2 q2).
      
Abort.


Program Definition mul_poly (p q:valid_pol) := {|VP_value := mul_poly_ (VP_value p) (VP_value q) ; VP_prop := _ |}.
Admit Obligations.


Definition sub_poly (p q:valid_pol) := sum_poly p (mul_poly (cst_poly (-1)%Z) q).

Fixpoint to_poly (f:form) (val:nat->bool) := 
  match f with 
  |f_true => cst_poly 1%Z
  |f_false => cst_poly 0%Z
  |f_and a b => mul_poly (to_poly a val) (to_poly b val)
  |f_or a b => sub_poly (sum_poly (to_poly a val) (to_poly b val)) (mul_poly (to_poly a val) (to_poly b val))
  |f_not a =>  sub_poly (cst_poly 1%Z) (to_poly a val)
  |f_var n => if (val n) then cst_poly 1%Z else cst_poly 0%Z 
(* |f_imp a b => sub_poly (sum_poly (sub_poly (cst_poly 1%Z) (to_poly a val)) (to_poly b val)) (mul_poly (sub_poly (cst_poly 1%Z) (to_poly a val)) (to_poly b val)) *)
end.


Lemma mul_pol_1 : forall (p:poly), (mul_poly_ (Cst 1) p)  = p .
Proof.
  intros.
  induction  p.
  - simpl. destruct z; trivial.
  - simp mul_poly_. 
    simpl.
    rewrite IHp1.
    rewrite IHp2.
    reflexivity.
Qed. 

Lemma mul_pol_0 : forall (p:poly) (val:nat -> Z), Z.eq (poly_val_ (mul_poly_ (Cst 0) p) val)  0%Z .
Proof.
  intros.
  induction  p.
  - simp mul_poly_. simpl. intuition.
  - simp mul_poly_. 
    simpl.
    rewrite IHp1.
    rewrite IHp2.
    simpl.
    rewrite Z.mul_0_r.
    intuition.
Qed. 

Lemma mul_pol_1_r : forall (p:poly),  (mul_poly_ p (Cst 1))  = p .
Proof.
  intros.
  induction  p.
  - simp mul_poly_.  rewrite Z.mul_1_r. reflexivity.
  - simp mul_poly_. 
    rewrite mul_pol_1.
    rewrite mul_pol_1.
    reflexivity.
Qed.

Lemma mul_pol_0_r : forall (p:poly) (val:nat -> Z), Z.eq (poly_val_ (mul_poly_ p (Cst 0)) val)  0%Z .
Proof.
  intros.
  induction  p.
  - simp mul_poly_.  rewrite Z.mul_0_r. reflexivity.
  - simp mul_poly_. 
    simpl.
    rewrite mul_pol_0.
    rewrite mul_pol_0.
    simpl.
    rewrite Z.mul_0_r.
    reflexivity.
Qed.


Hint Rewrite Z.mul_0_r : core.

Require Import Lia.

Definition z_of_bool := (fun x : bool => if x then 1%Z else 0%Z).



Lemma mul_poly_val (p q : valid_pol) (val:nat->Z) : 
(poly_val (mul_poly p q) val)%Z  = ((poly_val p val) * (poly_val q val))%Z.
Proof.
  destruct p as ( p & ? ).
  destruct q as ( q & ? ).
  unfold poly_val.
  unfold mul_poly.
  simpl.
  induction p.
  - unfold poly_val. simpl. induction q. simpl. 
    + reflexivity.
    + apply valid_b_more in VP_prop1.
Abort.
