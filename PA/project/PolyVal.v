Require Import definitions.
Import ZArith NatMap F P.
Require Import Coeff BoolHelp PolyArith Valid.
Import Bool Equations.
Require Import Lia.
Definition empty : monoid := NatMap.empty nat.

Fixpoint poly_val_ (pol:poly) (f : nat -> Z) := 
  match pol with 
  | Cst z => z
  | Poly p i q => 
    Z.add (poly_val_ p f) (Z.mul (f i) (poly_val_ q f))
end.

Definition poly_val (pol:valid_pol) (f : nat -> Z) := 
 poly_val_ (VP_value pol) f 
.

Lemma poly_val_empty (p : poly) :
  valid_b p = true -> 
    (poly_val_ p (fun _ => 0))%Z = get_coefficient_ p empty.
Proof.
  intro.
  induction p.
  - unfold get_coefficient_.
    unfold poly_val_.
    unfold for_all. rewrite P.fold_Empty; intuition. apply empty_1.
  - valid_destr H.
    specialize (IHp1 V0). specialize (IHp2 V1).
    simpl.
    rewrite <- Zred_factor6.
    rewrite IHp1.
    reflexivity.
Qed.

Goal poly_val_ (Poly (Cst 0) 0 (Cst 1)) (fun n => List.nth n (1%Z::nil) 0%Z) = 1%Z.
simpl.
Abort.


Definition val_of_mono (m : monoid) : nat -> Z := 
fun n => match find n m with |Some n0 => Z.of_nat n0 |None => 0%Z end
.

Lemma val_of_mono_correct (m:monoid) (p:poly) : 
valid_b p = true -> get_coefficient_ p m = poly_val_ p (val_of_mono m)
.
Proof.
  intros.
  induction p.
  - simpl.  
Abort.


Lemma notnull_not0_valuation (p q:poly) (i:nat) : 
valid_b (Poly p i q) = true ->  exists (val:nat->Z), poly_val_ (Poly p i q) val <> 0%Z  /\ (val i > 0)%Z 
.
Proof.
(*   intros.
  revert p H.  
  
  induction q; intros.
  - apply valid_b_not_null_r in H as NNp. 
    destruct (b_dec (is_null p) true).
    + exists (fun n => if n =? i then 1%Z else 0%Z).
      simpl.
      split.
      rewrite poly_val_null; [|assumption].
      * rewrite Nat.eqb_refl. destruct z.
        destruct p; inversion H.
        lia. lia.
      * rewrite Nat.eqb_refl. lia.
    + admit.
  - valid_destr H.
    apply valid_b_not_null_r in V2 as NNq2. *)
    (* specialize (IHq2 V3 NNq2). *)

Abort.


Lemma notnull_not0_valuation (p:poly) : 
valid_b p = true -> is_null p = false -> exists (val:nat->Z), poly_val_ p val <> 0%Z  
.
Proof.
  intros.
  induction p.
  - destruct z.
    + inversion H0.
    + exists (fun _ => 0%Z). simpl. intuition.
    + exists (fun _ => 0%Z). simpl. intuition.
  - valid_destr H. specialize (IHp1 V0). specialize (IHp2 V1).
    apply valid_b_not_null_r in H as NNp.
    specialize (IHp2 NNp).
    
    destruct (b_dec (is_null p2) true).
    + destruct IHp2.
      exists x.
      (* eapply poly_val_null with (val:=x) in H1.
      simpl.
      rewrite H1. *)

Abort.


Lemma val_is_cst (p:poly) (z:Z): valid_b p = true -> (forall (f: nat -> Z), poly_val_ p f = z ) -> 
 p = (Cst z).
Proof.
  intro.
  induction p.
  - intros.
    elim (Z.eq_dec z0 z); intro.
    + rewrite a in *.  reflexivity.
    + exfalso. apply b. 
      specialize (H0 (fun x => 0%Z)). simpl in H0.
      auto.
  - intros.
    valid_destr H.
    specialize (IHp1 V0). specialize (IHp2 V1).
    specialize H0 as Hz.
    specialize (H0 (fun _=> 0%Z)).
    simpl in H0.
    rewrite Z.add_0_r in H0.

    elim (Z.eq_dec z 0); intro.
    + rewrite a in *.
      eapply coeffNot0 in H as H1.
      destruct H1.
      destruct H1.
      destruct H2.
      erewrite coeff_remove_l with (n:=x0) in H1; try assumption.
      
      simpl in H0.
      simpl in H0.


    admit.
    

Admitted.


Theorem val_coeff (p q : valid_pol) : (forall (f:nat -> Z), poly_val p f = poly_val q f) -> (forall (m: monoid ), get_coefficient p m = get_coefficient q m).
Proof.
  intros.
  destruct p as [p ].
  destruct q as [q ].
  
  unfold get_coefficient.
  unfold VP_value.
  unfold poly_val in H.
  unfold VP_value in H.
  revert m  p VP_prop H .

  induction q.
  - intros. 
    simpl in H.
    apply val_is_cst in H. rewrite H. reflexivity. 
    assumption.
  - intros.

    edestruct (option_dec (find n m)).
    + 
      
Admitted.


Lemma valid_remove_null (p:poly) : 
valid_b p = true ->
remove_null_r p = p.
Proof.
  intro.
  induction p.
  - simpl. reflexivity.
  - simpl.
    valid_destr H.
    elim (b_dec (is_null (remove_null_r p2)) true); intro.
    + apply is_null_is_0 in H0 as H1. rewrite (IHp2 V1) in H1.
      rewrite H1 in H.
      destruct p1; inversion H.
    + rewrite not_true_iff_false in H0.
      rewrite H0.
       rewrite (IHp1 V0).
       rewrite (IHp2 V1).
       reflexivity.
Qed.

Lemma null_sum_dec (p q : poly) : 
  is_null p = true -> is_null q = true -> is_null (remove_null_r (sum_poly_ p q)) = true.
Proof.
  intros.
  rewrite is_null_is_0 in H. rewrite is_null_is_0 in H0.
  rewrite H. rewrite H0. simp sum_poly_. simpl. reflexivity.
Qed.




Lemma remove_null_remove_null (p:poly): (remove_null_r p) = (remove_null_r (remove_null_r p)) .
Proof.
  induction p.
  - simpl. reflexivity.
  - simpl.
    elim (b_dec (is_null (remove_null_r p2)) true); intro.
    + rewrite H. assumption.
    + rewrite not_true_iff_false in H. rewrite H. simpl.
      rewrite <- IHp2.
      rewrite H.
      rewrite <- IHp1.
      reflexivity.
Qed.

Lemma poly_val_remove_null_r (p:poly) (f:nat->Z) : poly_val_ (remove_null_r p) f = poly_val_ p f.
Proof.
  induction p; simpl.
  reflexivity.
  destruct (b_dec (is_null (remove_null_r p2)) true).
  - rewrite H. 
    rewrite IHp1.
    rewrite <- IHp2.
    rewrite is_null_is_0 in H.
    rewrite H.
    simpl. lia.
  - rewrite not_true_iff_false in H.
    rewrite H.
    simpl.
    rewrite IHp1. rewrite IHp2.
    reflexivity.
Qed.


Lemma sum_poly_val (p q : valid_pol) (val:nat->Z) : 
(poly_val (sum_poly p q) val)  = ((poly_val p val) + (poly_val q val))%Z.
Proof.
  destruct p as (p & VP).
  destruct q as (q & VQ).
  unfold poly_val.
  unfold sum_poly.
  simpl.
  rewrite poly_val_remove_null_r.
  revert q VQ. 
  induction p.
  - simpl. induction q; intros; simp sum_poly_; simpl. 
    + reflexivity.
    + valid_destr VQ.
      specialize (IHq1 V0). specialize (IHq2 V1).
      apply valid_b_not_null_r in VQ as H.
      rewrite IHq1.
      lia.
  - valid_destr VP. specialize (IHp1 V0).  specialize (IHp2 V1).
    simpl.
    apply valid_b_not_null_r in VP as H.
    
    induction q; simp sum_poly_; intro; simpl.
    + rewrite IHp1.
      simpl.
      lia.
      auto.
    + valid_destr VQ.
      specialize (IHq1 V2). specialize (IHq2 V3).
      apply valid_b_not_null_r in VQ as H0.
      
      elim (gt_eq_gt_dec n0 n); intro.
      * elim a; intro.
        -- apply nat_compare_gt in a0 as a1.
          rewrite a1.
          rewrite sum_pol_sym; try assumption.
          simpl.
          rewrite IHq1.
          lia.

        -- rewrite b in *. rewrite Nat.compare_refl.
          specialize H0 as NN.
          simpl.
          simpl in IHp1.
          simpl in IHp2.
          rewrite IHp1. rewrite IHp2.
          simpl. lia.
          assumption. assumption.
    * apply nat_compare_lt in b.
      rewrite b.
      simpl.
      rewrite IHp1.
      simpl.
      lia.
      assumption.
Qed.




Lemma mul_poly_val (p q : valid_pol) (val:nat->Z) : 
(poly_val (mul_poly p q) val)%Z  = ((poly_val p val) * (poly_val q val))%Z.
Proof.
  destruct p as ( p & VP ).
  destruct q as ( q & VQ ).
  unfold poly_val.
  unfold mul_poly.
  simpl.
  
  revert q VQ. 
  induction p; intros; simpl.
  - rewrite poly_val_remove_null_r. 
    induction q; simpl. 
    + reflexivity.
    + valid_destr VQ.
      specialize (IHq1 V0). specialize (IHq2 V1).
      simp mul_poly_. simpl.
      rewrite IHq1. rewrite IHq2. lia.
  - valid_destr VP.  specialize (IHp1 V0). specialize (IHp2 V1).
   induction q; simp mul_poly_. 
    + rewrite poly_val_remove_null_r. 
      specialize (IHp1 (Cst z)).
      rewrite poly_val_remove_null_r in IHp1.
      specialize (IHp2 (Cst z)).
      rewrite poly_val_remove_null_r in IHp2.
      simpl.
      rewrite IHp1. rewrite IHp2.
      simpl. lia.
      trivial. trivial.
    + valid_destr VQ.
      elim (gt_eq_gt_dec n0 n); intro.
      * elim a; intro.
      -- apply nat_compare_gt in a0 as a1.
        rewrite a1.
        rewrite poly_val_remove_null_r.
        simpl.
        rewrite poly_val_remove_null_r in IHq1.
        rewrite poly_val_remove_null_r in IHq2.
        rewrite IHq1.
        rewrite IHq2.
        lia.
        assumption.
        assumption.
      -- rewrite b in *. rewrite Nat.compare_refl.
        rewrite poly_val_remove_null_r.
        simpl.
        simp sum_poly_.
        rewrite Nat.compare_refl.
        rewrite poly_sum0.
        simp sum_poly_.
        rewrite Nat.compare_refl.
        simpl.
        rewrite poly_sum0.
        simpl.
        specialize (IHp1 q1) as IHp1q1.
        rewrite poly_val_remove_null_r in IHp1q1.
        rewrite IHp1q1; [|assumption].
        simpl.
        rewrite Z.mul_add_distr_r.
        rewrite Z.mul_add_distr_l.
        rewrite <- Z.add_assoc.
        rewrite Z.add_cancel_l.

        admit.
        
  * apply nat_compare_lt in b.
  rewrite poly_val_remove_null_r. 
    rewrite b.
    simpl.
    specialize (IHp1 (Poly q1 n0 q2)).
    rewrite poly_val_remove_null_r in IHp1. 
    rewrite IHp1.
    simpl.
    specialize (IHp2 (Poly q1 n0 q2)).
    rewrite poly_val_remove_null_r in IHp2. 
    rewrite IHp2.
    simpl.
    lia.
    assumption.
    assumption.
Admitted.


