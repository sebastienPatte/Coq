Require Import Valid.
Require Import definitions.
Require Import BoolHelp.

Import ZArith Arith Bool Lia.
Import FMapList .
Import P.
Import F.
Import NatMap.
Import Coq.FSets.FMapFacts.
From Equations Require Import Equations. 

Definition is_null (p:poly) : bool := 
  match p with 
  |Cst 0 => true 
  |_=> false 
  end
.

Lemma is_null_is_0 (p:poly) : is_null p = true <-> p = Cst 0 .
Proof.
  unfold iff.
  split.
  - destruct p; intro.
    + destruct z. reflexivity. inversion H. inversion H.
    + inversion H.
  - destruct p; intro.
  + destruct z. trivial.  inversion H. inversion H.
  + inversion H.
Qed.

Lemma valid_b_not_null_r (p q:poly) (i:nat) : valid_b (Poly p i q) = true -> is_null q = false. 
Proof.
  intro.  
  rewrite <- not_true_iff_false.  
  intro.
  rewrite is_null_is_0 in H0.
  rewrite H0 in H.
  destruct p; inversion H.
Qed.


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



Fixpoint remove_null_r (pol:poly) : poly :=
  match pol with 
  |Cst z => Cst z
  |Poly p i q => 
  if is_null (remove_null_r q) then (remove_null_r p)
  else Poly (remove_null_r p) i (remove_null_r q) 
  end
.

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

Lemma weak_sum_pol_sym (p q:poly) : 
weak_valid_b p = true -> 
weak_valid_b q = true -> 
sum_poly_ p q = sum_poly_ q p.
Proof.
  revert q.
  induction p; intros.
  - induction q; simp sum_poly_. 
    + apply f_equal. intuition.
    + weak_valid_destr H0. rewrite (IHq1 V0). apply f_equal. reflexivity.
  - weak_valid_destr H. 
    specialize (IHp1 q V0 H0) as HQ1. 
    specialize (IHp2 q V1 H0) as HQ2.
    destruct q; simp sum_poly_.
    + rewrite HQ1. reflexivity.
    + elim (gt_eq_gt_dec n n0); intro.
      * elim a; intro.
        -- apply nat_compare_gt in a0 as a_gt.  
          apply nat_compare_lt in a0 as a_lt.  
          rewrite a_gt. 
          rewrite a_lt. reflexivity.
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

Lemma sum_pol_sym (p q:poly) : 
valid_b p = true -> 
valid_b q = true -> 
sum_poly_ p q = sum_poly_ q p.
Proof.
  intros.
  apply weaken_valid in H.
  apply weaken_valid in H0.
  apply weak_sum_pol_sym; assumption.
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

Lemma lt_inv_le (n n0 : nat) : (n0 ?= n) = Lt <-> (n ?= n0) = Gt.
Proof.
  unfold iff; split; intro.
  - apply nat_compare_lt in H. apply nat_compare_gt in H. assumption.
  - apply nat_compare_gt in H. apply nat_compare_lt in H. assumption.
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
  destruct p2, q2; intros; simp sum_poly_.
  - trivial.
  - apply weak_valid_leq in H0. auto.
  - apply weak_valid_leq in H. auto.
  - apply weak_valid_leq in H. apply weak_valid_leq in H0.  destruct (n ?= n1); auto.
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
  destruct p1, q1; intros; simp sum_poly_.
  - trivial.
  - apply weak_valid_le in H0. auto.
  - apply weak_valid_le in H. auto.
  - apply weak_valid_le in H. apply weak_valid_le in H0.  destruct (n ?= n1); auto.
Qed.

Lemma weak_sum_leq' (p1 p2 q1 q2 p q:poly) (n0:nat): 
weak_valid_b (Poly p1 n0 p2) = true ->
weak_valid_b (Poly q1 n0 q2) = true -> 
weak_valid_b (Poly p n0 q) = true ->
weak_valid_b (sum_poly_ p2 q2) = true -> 
weak_valid_b (Poly p n0 (sum_poly_ p2 q2)) = true
.
Proof.
  intros.
  assert (aaa : match sum_poly_ p2 q2 with 
  |Cst _ => true 
  |Poly _ j _ => n0 <=? j 
  end = true).
  eapply weak_sum_leq with (p1:=p1) (q1:=q1); try assumption. 
  destruct (sum_poly_ p2 q2). 
  - simpl. destruct p. trivial. andb_split. apply weak_valid_le in H1. auto. weak_valid_destr H1. assumption.
  - eapply leq_weak_valid; intuition.
Qed.

Lemma weak_sum_gt' (p1 p2 q1 q2 p q:poly) (n0:nat): 
weak_valid_b (Poly p1 n0 p2) = true ->
weak_valid_b (Poly q1 n0 q2) = true -> 
weak_valid_b (Poly p n0 q) = true ->
weak_valid_b (sum_poly_ p1 q1) = true -> 
weak_valid_b (Poly (sum_poly_ p1 q1) n0 q) = true
.
Proof.
  intros.
  assert (aaa : match sum_poly_ p1 q1 with 
  |Cst _ => true 
  |Poly _ j _ => n0 <? j 
  end = true).
  eapply weak_sum_gt with (p2:=p2) (q2:=q2); try assumption. 
  destruct (sum_poly_ p1 q1). 
  - simpl. destruct q. trivial. andb_split. apply weak_valid_leq in H1. auto. weak_valid_destr H1. assumption.
  - eapply le_weak_valid; intuition.  
Qed.

Lemma sum_weak_valid (p q:poly) : weak_valid_b p = true -> weak_valid_b q = true -> weak_valid_b (sum_poly_ p q) = true.
Proof.
  intros VP VQ.
  revert q VQ.
  induction p; intros.
  - induction q; simp sum_poly_. 
    weak_valid_destr VQ. specialize (IHq1 V0). specialize (IHq2 V1).
    simp sum_poly_.
    apply weak_valid_sum_cst_p; assumption.
  - weak_valid_destr VP. specialize (IHp1 V0). specialize (IHp2 V1).
    induction q; simp sum_poly_.
    + specialize (IHp1 (Cst z) VQ).
      rewrite weak_sum_pol_sym in IHp1; try assumption.
      rewrite weak_sum_pol_sym; try assumption.
      apply weak_valid_sum_cst_p; assumption.
    + weak_valid_destr VQ. specialize (IHq1 V2). specialize (IHq2 V3).
      elim (gt_eq_gt_dec n n0); intro.
      * elim a; intro.
        -- eapply nat_compare_lt in a0 as a1.
          rewrite a1.
          eapply le_weak_valid with (p:=q1) (q:=q2) (p':=p1) (q':=p2) in a0 as a2; try assumption.
          specialize (IHp1 (Poly q1 n0 q2) VQ) as HN1.
          eapply weak_sum_gt' with (p2:=p2) (q2:=p2) (p:=p1); assumption.
        -- rewrite b in *. rewrite Nat.compare_refl.
          specialize (IHp1 q1 V2) as HN1.
          specialize (IHp2 q2 V3) as HN2.
          eapply weak_sum_gt' with (p2:=p2) (q2:=q2) (p:=p1); try assumption.
          eapply weak_sum_leq' with (p1:=p1) (q1:=q1) (q:=p2); try assumption. 
    * apply nat_compare_gt in b as b1.
      rewrite b1.
      eapply weak_sum_gt' with (p2:=q2) (q2:=q2) (p:=q1); try assumption.
      eapply le_weak_valid with (p':=q1); try assumption.
      rewrite weak_sum_pol_sym; assumption.
Qed.

Lemma remove_null_remove_r (p q :poly) (i:nat) : 
  is_null q = true -> 
   remove_null_r (Poly p i q) = (remove_null_r p).
Proof.
  simpl.
  intros.
  destruct q. 
  - simpl in H. destruct z. reflexivity.  inversion H. inversion H.
  - simpl in H. inversion H.
Qed.



Lemma not_null_le (p q:poly) (i:nat) : 
weak_valid_b (Poly p i q) = true ->
is_null (remove_null_r p) = false -> 
match (remove_null_r p) with 
|Cst 0 => false 
|Cst _ => true 
|Poly _ j _ => i <? j
end = true.
Proof.
  intros.
  induction p.
  - simpl.
  destruct z.
  inversion H0.
  reflexivity.
  reflexivity.
  - simpl.
    elim (b_dec (is_null (remove_null_r p2)) true); intro.
    + rewrite H1.
      simpl in H0. 
      rewrite H1 in H0.
      destruct (remove_null_r p1).
      destruct z.
      inversion H0.
      reflexivity.
      reflexivity.
      apply IHp1.
      weak_valid_destr H. assumption.
      trivial.
    + rewrite not_true_iff_false in H1.
      rewrite H1. rewrite H1 in IHp2.
      apply weak_valid_le in H.
      auto.
Qed.

Lemma weak_valid_rem (p q1 q2 :poly) (i j:nat): 
weak_valid_b (Poly p i (Poly q1 j q2)) = true -> weak_valid_b (Poly p i q1) = true.
Proof.
  intro.
  induction p.
  - simpl in *.
    andb_destr H.
    destruct q1.
    destruct q2.
    reflexivity.
    reflexivity.
    andb_split.
    destruct q2.
    andb_destr H0.
    apply leb_trans with (j:=j). auto.
    andb_destr H0.
    apply leb_trans with (j:=j). auto.
    destruct q2; andb_destr H0; assumption.
  - weak_valid_destr H.
    intuition.
    destruct q1.
    + simpl.
      andb_split.
      apply weak_valid_le in H. auto.
      simpl in V2.
      assumption.
    + apply weak_valid_leq in V4 as leq1.
      apply weak_valid_le in V3 as le1.
      apply weak_valid_le in H as le2.
      simpl.
      andb_split.
      auto.
      apply leb_trans with (j:=j). auto.
      assumption.
      simpl in H0.
      destruct p1.
      andb_destr H0.
      assumption.
      andb_destr H0.
      assumption.
Qed.


Lemma not_null_leq (p q:poly) (i:nat) : 
weak_valid_b (Poly p i q) = true ->
is_null (remove_null_r q) = false -> 
match (remove_null_r q) with 
|Cst 0 => false 
|Cst _ => true 
|Poly _ j _ => i <=? j
end = true.
Proof.
  intros.
  induction q.
  - simpl.
  destruct z.
  inversion H0.
  reflexivity.
  reflexivity.
  - simpl.
    elim (b_dec (is_null (remove_null_r q2)) true); intro.
    + rewrite H1.
      simpl in H0. 
      rewrite H1 in H0.

      destruct (remove_null_r q1).

      destruct z.
      inversion H0.
      reflexivity.

      reflexivity.
      apply weak_valid_rem in H.

      apply IHq1.
      assumption.
      assumption.
    + rewrite not_true_iff_false in H1.
      simpl in H0.
      rewrite H1 in *.
      weak_valid_destr H.
      intuition.
      apply weak_valid_leq in V0.
      auto.
Qed.

Lemma strengthen_valid (p:poly) : weak_valid_b p = true -> valid_b (remove_null_r p) = true .
Proof.
  intro.
  induction p.
  - simpl. reflexivity.
  - weak_valid_destr H.
    elim (b_dec (is_null (remove_null_r p2)) true); intro.
    + specialize (IHp1 V0). simpl remove_null_r. rewrite H0. assumption. 
    + rewrite not_true_iff_false in H0.
      simpl.
      intuition.
      rewrite H0.
      eapply not_null_leq with (i:=n) (p:=p1) in H0.

      destruct (remove_null_r p2).
      * destruct z. inversion H0. 
        -- elim (b_dec (is_null (remove_null_r p1)) true); intro.
          ++ rewrite is_null_is_0 in H3. rewrite H3.
            simpl remove_null_r.
            simpl. 
            reflexivity.
          ++ rewrite not_true_iff_false in H3.
            intuition.
            eapply not_null_le with (i:=n) (q:=p2) in H3.
            destruct (remove_null_r p1).
            destruct z. inversion H1.
            reflexivity. 
            reflexivity.
            reflexivity.
            eapply le_valid with (p':=Cst 0). 
            intuition.
            assumption.
            simpl. reflexivity.
            assumption.
        --  elim (b_dec (is_null (remove_null_r p1)) true); intro.
        ++ rewrite is_null_is_0 in H3. rewrite H3.
          simpl remove_null_r.
          simpl. 
          reflexivity.
        ++ rewrite not_true_iff_false in H3.
          intuition.
          eapply not_null_le with (i:=n) (q:=p2) in H3.
          destruct (remove_null_r p1).
          destruct z. inversion H3.
          reflexivity. 
          reflexivity.
          eapply le_valid with (p':=Cst 0). 
          intuition.
          assumption.
          simpl. reflexivity.
          assumption.
        * elim (b_dec (is_null (remove_null_r p1)) true); intro.
          -- rewrite is_null_is_0 in H3. rewrite H3.
            eapply leq_valid with (q:=Cst 1).
            auto.
            simpl. reflexivity.
            intuition.
          -- rewrite not_true_iff_false in H3.
            intuition.
            eapply not_null_le with (i:=n) (q:=p2) in H3.
            destruct (remove_null_r p1).
            destruct z.
            inversion H3.

            simpl remove_null_r; eapply leq_valid with (q:=Cst 1); intuition.
            simpl remove_null_r; eapply leq_valid with (q:=Cst 1); intuition.
        
            andb_split; auto.
            assumption.
        * assumption.
Qed.


Lemma is_null_remove_null_r (p:poly) : is_null p = true -> is_null (remove_null_r p) = true.
Proof.
  intro.
  destruct p.
  - simpl. destruct z. reflexivity.  inversion H. inversion H.
  - simpl in H. inversion H. 
Qed.

Lemma is_null_dec (p q :poly) (i:nat) : is_null (remove_null_r (Poly p i q)) = true -> 
is_null (remove_null_r (q)) = true /\ is_null (remove_null_r p) = true.
Proof.
  revert q.
  induction p; intros.
  - simpl in H.
    elim (b_dec (is_null (remove_null_r q)) true); intro.
    + split. assumption. rewrite H0 in H. assumption.
    + rewrite not_true_iff_false in H0.
      rewrite H0 in H.
      inversion H.

  - simpl in H.
  elim (b_dec (is_null (remove_null_r q)) true); intro.
    + split. assumption. 
      simpl. rewrite H0 in *. assumption.
    + rewrite not_true_iff_false in H0.
      rewrite H0 in *.
      inversion H.
Qed.


Lemma sum_valid (p q:poly) : valid_b p = true -> valid_b q = true -> valid_b (remove_null_r (sum_poly_ p q)) = true.
Proof.
  intros.
  apply strengthen_valid.
  apply weaken_valid in H.
  apply weaken_valid in H0.
  apply sum_weak_valid; assumption.
Qed.


Program Definition sum_poly (p q:valid_pol) := {|VP_value := remove_null_r (sum_poly_ (VP_value p) (VP_value q)) ; VP_prop := _ |}.
Next Obligation.
  destruct p as [p VP].
  destruct q as [q VQ].
  unfold VP_value.
  apply sum_valid; assumption.
Qed.


Equations mul_poly_ (p q:poly) : poly by wf (length p + length q) :=
  mul_poly_ (Cst z1) (Cst z2) := Cst (z1 * z2);
  mul_poly_ (Poly p1 i q1) (Cst z2) := Poly (mul_poly_ p1 (Cst z2)) i (mul_poly_ q1 (Cst z2));
  mul_poly_ (Cst z1) (Poly p2 j q2) := Poly (mul_poly_ (Cst z1) p2 ) j (mul_poly_ (Cst z1) q2 );
  mul_poly_ (Poly p1 i q1) (Poly p2 j q2) :=
    match Nat.compare i j with
    |Eq => sum_poly_ (sum_poly_ 
      (Poly (mul_poly_ p1 p2) i (Poly (Cst 0) i (mul_poly_ q1 q2))) 
      (Poly (Cst 0) i (mul_poly_ p1 q2))) 
      (Poly (Cst 0) i (mul_poly_ p2 q1)) 
    |Lt => Poly (mul_poly_ p1 (Poly p2 j q2)) i (mul_poly_ q1 (Poly p2 j q2))
    |Gt => Poly (mul_poly_ (Poly p1 i q1) p2) j (mul_poly_ (Poly p1 i q1) q2)
    end
.

Goal mul_poly_ (Cst 0) (Poly (Cst (0)) 0 (Cst 2)) = (Cst 0).
  simp mul_poly_; simpl.
  simp sum_poly_. simpl.
Abort.

Goal mul_poly_ (Poly (Cst (-2%Z)) 0 (Cst 2)) (Poly (Cst 3) 0 (Cst 1)) = Poly (Cst (-6)) 0 (Poly (Cst 4) 0 (Cst 2)).
  simp mul_poly_. simpl.
  simp sum_poly_. simpl.
  simp sum_poly_. simpl.
Abort.


Lemma weak_mul_leq (p1 p2 q1 q2:poly) (n0:nat): 
weak_valid_b (Poly p1 n0 p2) = true ->
weak_valid_b (Poly q1 n0 q2) = true -> 
match mul_poly_ p2 q2 with 
|Cst _ => true 
|Poly _ j _ => n0 <=? j 
end = true
.
Proof.
  destruct p2, q2; intros; simp mul_poly_; simp sum_poly_.
  - trivial.
  - apply weak_valid_leq in H0. auto.
  - apply weak_valid_leq in H. auto.
  - apply weak_valid_leq in H. apply weak_valid_leq in H0. 
  rewrite Nat.compare_refl. destruct (n ?= n1); auto.
  simp sum_poly_. rewrite Nat.compare_refl. auto.
Qed.

Lemma weak_mul_gt (p1 p2 q1 q2:poly) (n0:nat): 
weak_valid_b (Poly p1 n0 p2) = true ->
weak_valid_b (Poly q1 n0 q2) = true -> 
match mul_poly_ p1 q1 with 
|Cst _ => true 
|Poly _ j _ => n0 <? j 
end = true
.
Proof.
  destruct p1, q1; intros; simp mul_poly_; simp sum_poly_.
  - trivial.
  - apply weak_valid_le in H0. auto.
  - apply weak_valid_le in H. auto.
  - apply weak_valid_le in H. apply weak_valid_le in H0. rewrite Nat.compare_refl. destruct (n ?= n1); auto.
  simp sum_poly_. rewrite Nat.compare_refl. auto.
Qed.

Lemma weak_mul_leq' (p1 p2 q1 q2 p q:poly) (n0:nat): 
weak_valid_b (Poly p1 n0 p2) = true ->
weak_valid_b (Poly q1 n0 q2) = true -> 
weak_valid_b (Poly p n0 q) = true ->
weak_valid_b (mul_poly_ p2 q2) = true -> 
weak_valid_b (Poly p n0 (mul_poly_ p2 q2)) = true
.
Proof.
  intros.
  assert (aaa : match mul_poly_ p2 q2 with 
  |Cst _ => true 
  |Poly _ j _ => n0 <=? j 
  end = true).
  eapply weak_mul_leq with (p1:=p1) (q1:=q1); try assumption. 
  destruct (mul_poly_ p2 q2). 
  - simpl. destruct p. trivial. andb_split. apply weak_valid_le in H1. auto. weak_valid_destr H1. assumption.
  - eapply leq_weak_valid; intuition.
Qed.

Lemma weak_mul_gt' (p1 p2 q1 q2 p q:poly) (n0:nat): 
weak_valid_b (Poly p1 n0 p2) = true ->
weak_valid_b (Poly q1 n0 q2) = true -> 
weak_valid_b (Poly p n0 q) = true ->
weak_valid_b (mul_poly_ p1 q1) = true -> 
weak_valid_b (Poly (mul_poly_ p1 q1) n0 q) = true
.
Proof.
  intros.
  assert (aaa : match mul_poly_ p1 q1 with 
  |Cst _ => true 
  |Poly _ j _ => n0 <? j 
  end = true).
  eapply weak_mul_gt with (p2:=p2) (q2:=q2); try assumption. 
  destruct (mul_poly_ p1 q1). 
  - simpl. destruct q. trivial. andb_split. apply weak_valid_leq in H1. auto. weak_valid_destr H1. assumption.
  - eapply le_weak_valid; intuition.  
Qed.

Lemma weak_val_mul_gt (p2 p3 q1 q2 : poly) (n n0:nat) : 
  n > n0 ->
  weak_valid_b (Poly p2 n p3) = true ->
  weak_valid_b (Poly q1 n0 q2) = true ->
  weak_valid_b (mul_poly_ p2 (Poly q1 n0 q2)) = true ->
  weak_valid_b (mul_poly_ p3 (Poly q1 n0 q2)) = true ->
    
     (weak_valid_b (mul_poly_ p2 q1) = true /\ weak_valid_b (mul_poly_ p2 q2) = true )
  /\ (weak_valid_b (mul_poly_ p3 q1) = true /\ weak_valid_b (mul_poly_ p3 q2) = true )
.
Proof.
  intros.
  split.
  - destruct p2.
  simp mul_poly_ in *.
  weak_valid_destr H2.
  split; assumption.
  simp mul_poly_ in *.
  apply weak_valid_le in H0.
  assert (aa :  n0 < n1).
  eapply Nat.lt_trans with (m:=n); auto.
  rewrite <- Nat.compare_gt_iff in aa.
  rewrite aa in H2.
  weak_valid_destr H2.
  split; assumption.
  - destruct p3.
  simp mul_poly_ in *.
  weak_valid_destr H3.
  split; assumption.
  simp mul_poly_ in *.
  apply weak_valid_leq in H0.
  assert (aa :  n0 < n1).
  eapply Nat.lt_le_trans with (m:=n); auto.

  rewrite <- Nat.compare_gt_iff in aa.
  rewrite aa in H3.
  weak_valid_destr H3.
  split; assumption.
Qed.

Lemma poly_sum0 (p:poly) : sum_poly_ p (Cst 0) = p.
Proof.
  induction p.
  - simp sum_poly_. rewrite Z.add_0_r. reflexivity.
  - simp sum_poly_. rewrite IHp1. reflexivity. 
Qed.

Lemma weak_val_mul_eq (p2 p3 q1 q2 : poly) (n n0:nat) : 
  n = n0 ->
  weak_valid_b (Poly p2 n p3) = true ->
  weak_valid_b (Poly q1 n0 q2) = true ->
  weak_valid_b (mul_poly_ p2 (Poly q1 n0 q2)) = true ->
  weak_valid_b (mul_poly_ p3 (Poly q1 n0 q2)) = true ->
    
     (weak_valid_b (mul_poly_ p2 q1) = true /\ weak_valid_b (mul_poly_ p2 q2) = true ) (* /\ weak_valid_b (mul_poly_ p3 q2) = true  *)
     (* /\ (weak_valid_b (mul_poly_ p3 q1) = true /\ weak_valid_b (mul_poly_ p3 q2) = true ) *)
     
      
.
Proof.
  intros.
  rewrite <- H in *.
  
  (* split. *)
  - destruct p2.
  simp mul_poly_ in *.
  weak_valid_destr H2.
  split; assumption.
  simp mul_poly_ in *.
  apply weak_valid_le in H0.
  rewrite <- Nat.compare_gt_iff in H0.
  rewrite H0 in H2.
  weak_valid_destr H2.
  split; assumption.

  (* - induction p3; intros.
    + simp mul_poly_ in *. weak_valid_destr H3. assumption.
    + simp mul_poly_ in *.
      simp sum_poly_ in *.
      rewrite Nat.compare_refl in H3.
      elim (gt_eq_gt_dec n n1); intro.
      * elim a; intro.
        -- apply nat_compare_gt in a0. rewrite a0 in H3.
          weak_valid_destr H3.
           assumption.
        -- rewrite <- b in *.
          rewrite Nat.compare_refl in H3.
          simp sum_poly_ in H3.
          rewrite Nat.compare_refl in H3.
          rewrite poly_sum0 in H3.
          rewrite poly_sum0 in H3.
          
          weak_valid_destr H3.
          weak_valid_destr H0. 
          intuition.

          admit.
        
      * apply weak_valid_leq in H0.
        intuition. *)
Admitted.

Lemma mul_poly_weak_valid (p q :poly) : 
weak_valid_b p = true ->
weak_valid_b q = true ->
weak_valid_b (mul_poly_ p q) = true 
.
Proof.
  revert q.
  induction p; intros.
  - induction q; simp mul_poly_.
    weak_valid_destr H0.
    intuition.
    eapply weak_mul_gt' with (p:=q1) (p2:=q2) (q2:=q2); try assumption.
    + simpl. destruct q2. reflexivity. andb_split. apply weak_valid_leq in H0. auto. assumption.
    
    + eapply weak_mul_leq' with (q1:=q1) (q:=q2) (p1:=q1); try assumption.
      destruct q1; simpl. reflexivity. andb_split. apply weak_valid_le in H0. auto. assumption.

  - weak_valid_destr H. specialize (IHp1 q V0 H0). specialize (IHp2 q V1 H0).
    induction q; simp mul_poly_; simp sum_poly_.
    + eapply weak_mul_gt' with (p:=p1) (p2:=p2) (q2:=p2); try assumption.
      * simpl. destruct p2. reflexivity. andb_split. apply weak_valid_leq in H. auto. assumption.
      * eapply weak_mul_leq' with (q1:=p1) (q:=p2) (p1:=p1); try assumption.
      destruct p1; simpl. reflexivity. andb_split. apply weak_valid_le in H. auto. assumption.
    
    + rewrite Nat.compare_refl.
      weak_valid_destr H. weak_valid_destr H0.
      elim (gt_eq_gt_dec n0 n); intro.
      * elim a; intro.
        -- apply nat_compare_gt in a0 as a1.
          rewrite a1.
            
          apply weak_val_mul_gt with (n:=n) (n0:=n0) (p2:=p1) (p3:=p2) (q1:=q1) (q2:=q2) in IHp1; try assumption.
          destruct IHp1. destruct H1,H2.
          eapply weak_mul_gt' with (p:=q1) (p2:=q2) (q2:=q2); try assumption.
          eapply le_weak_valid with (p':=q1); try assumption.
          eapply weak_mul_leq' with (p1:=q1) (q1:=q1) (q:=q2); try assumption.

          eapply leq_weak_valid with (q:=q2); auto.

          apply IHq2; try assumption.
          apply IHq1; try assumption.

      -- rewrite b in *.
        rewrite Nat.compare_refl.
        rewrite poly_sum0.
        simp sum_poly_.
        rewrite Nat.compare_refl.
        rewrite poly_sum0.
        
        eapply weak_val_mul_eq with (p2:=p1) (n:=n) (p3:=p2) in IHp1; auto.
        destruct IHp1.
        
        (* 
        eapply weak_sum_leq' with (q1:=q1) (q:=q2) (p1:=p2).
        eapply weak_sum_leq' with (q1:=q1) (q:=q2) (p1:=p2).
        eapply leq_weak_valid with (q:=p3); auto.

        eapply weak_mul_leq' with (q1:=q1) (q:=q2) (p1:=p2); auto.
        simpl. destruct q2. reflexivity. andb_split. apply weak_valid_leq in H0. auto. auto. 
         *)

        admit.
    * apply nat_compare_gt in b as b0.
      rewrite <- lt_inv_le in b0.
      rewrite b0.

      eapply weak_mul_gt' with (p:=p1) (p2:=p2) (q2:=p2); try assumption.
      eapply le_weak_valid with (p':=p1); try assumption.
      
      eapply weak_mul_leq' with (p1:=p1) (q1:=p1) (q:=p2); try assumption.

      eapply leq_weak_valid with (q:=p2); auto.
      
Admitted.


Program Definition mul_poly (p q:valid_pol) := {|VP_value := remove_null_r (mul_poly_ (VP_value p) (VP_value q)) ; VP_prop := _ |}.
Next Obligation.
  destruct p as [p VP].
  destruct q as [q VQ].
  unfold VP_value.
  apply weaken_valid in VP. apply weaken_valid in VQ.
  eapply (mul_poly_weak_valid p) in VQ as VPQ; [|assumption].
  apply strengthen_valid.
  assumption. 
Qed.

