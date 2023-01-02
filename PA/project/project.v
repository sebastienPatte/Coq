Require Import ZArith Bool.

Inductive poly : Type :=
| Cst : Z -> poly
| Poly : poly -> nat -> poly -> poly .

(* Fixpoint valid_b (p:poly) (i:nat) : bool := 
match p with 
|Cst _ => true
|Poly p j (Cst 0) => false
|Poly p j q => 
	Nat.leb i j && 
	valid_b p (S j) && valid_b q j 
end. 

Definition valid_bool (p:poly) : valid_b p 0. *)

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

Fixpoint valid_bool (pol:poly) : bool := 
match pol with 
|Cst _ => true
|Poly p i q => 
  match p,q with 
| _, (Cst 0) => false 
| (Cst _), (Cst _) => true 
| (Poly p1 j1 q1), (Cst _) => 
	Nat.ltb i j1 
  && valid_bool p 
| (Cst _),  (Poly p2 j2 q2) => 
	Nat.leb i j2 
  && valid_bool q 
|(Poly p1 j1 q1),  (Poly p2 j2 q2) => 
  Nat.ltb i j1 && Nat.leb i j2 
  && valid_bool p 
  && valid_bool q
  end 
end.

Lemma equivalence (p:poly) : valid_bool p = true <-> valid_poly p.
Proof.
  unfold iff. split.
  intro.
  - induction p.
  
  + econstructor.
  + induction p1,p2.
    * econstructor.
      simpl in H.
      unfold "<>".
      intro.
      rewrite H0 in H.
      intuition. 
    * simpl in H.
      intuition.
      rewrite andb_true_iff in H.
      destruct H. 
      econstructor.
      -- apply leb_complete.
        assumption.
      -- intuition.
    * intuition.
      simpl in H.
      destruct z; econstructor.
      -- intuition. 
      -- intuition.
      -- intuition.
      
      -- rewrite andb_true_iff in H.
        destruct H.
        apply leb_complete.
        intuition.
      -- intuition.
      -- rewrite andb_true_iff in H.
        destruct H.
        intuition.
      -- rewrite andb_true_iff in H.
      destruct H.
      apply leb_complete.
      intuition.
      -- intuition.
      -- 
       rewrite andb_true_iff in H.
        destruct H.
        intuition.
    * intuition.
      simpl in H.
      repeat (rewrite andb_true_iff in H).
      destruct H.
      destruct H.
      destruct H.
      econstructor.
      split; apply leb_complete; intuition.
      split.
      intuition.
      intuition.
  - 
    
    
  induction p;intros; inversion H.
    * intuition.
    
    * destruct y; intuition. 
    * destruct x; intuition.
      -- rewrite <- H0 in IHp1.
        apply IHp1 in H5.
      simpl.
      simpl in H5 .
      induction p; intuition.
      
      rewrite andb_true_iff.
      split.
      apply leb_correct; intuition.
      assumption.
      rewrite andb_true_iff.
      split.
      apply leb_correct; intuition.
      assumption.



      -- rewrite <- H0 in IHp1.
      apply IHp1 in H5.
      simpl.
      simpl in H5.
      induction p; intuition.
      rewrite andb_true_iff.
      split.
      apply leb_correct; intuition.
      assumption.
      rewrite andb_true_iff.
      split.
      apply leb_correct; intuition.
      assumption.
  * rewrite <- H3 in IHp2.
    apply IHp2 in H4.
    simpl.
    simpl in H4. 
    rewrite andb_true_iff.
    split.
    apply leb_correct; intuition.
    induction p; intuition.
  * destruct H4.
    rewrite <- H3 in IHp2.
    apply IHp2 in H5.
    rewrite <- H0 in IHp1.
    apply IHp1 in H4.
      simpl.
      simpl in H4.
      simpl in H5.
      rewrite andb_true_iff.
      split.
      rewrite andb_true_iff.
      split.
      rewrite andb_true_iff.
      split.
      apply leb_correct; intuition.
      apply leb_correct; intuition.
      
      induction p; intuition.
      induction p; intuition.
Qed.

Fixpoint valid_b (p:poly) (i:nat) : bool := 
match p with 
|Cst _ => true
|Poly p j (Cst 0) => false
|Poly p j q => 
	Nat.leb i j && 
	valid_b p (S j) && valid_b q j 
end. 

Lemma equiv (p:poly) : valid_b p 0 = true <-> valid_poly p.
Proof.
  unfold iff.
  induction p; split; intros.
  - econstructor.
  - simpl. reflexivity.
  - induction p1,p2.
    + econstructor.
      simpl in H.
      unfold "<>".
      intro.
      rewrite H0 in H.
      intuition. 
    + 
      intuition.
      simpl in H.

      destruct p2_2.
      * destruct z0.
        1: constructor; intuition.
        1-2: repeat (rewrite andb_true_iff in H; destruct H);  constructor;
          [apply leb_complete; intuition |
           apply H2; simpl; apply andb_true_iff; split; [
            assumption 
            | trivial
          ]].
      
      
      * repeat (rewrite andb_true_iff in H; destruct H);  constructor.
        -- apply leb_complete; intuition.
        -- apply H2; simpl; apply andb_true_iff; split.
          ** assumption.
          **  assumption.
      
    + intuition.
      simpl in H.
      destruct z; econstructor.
      * intuition. 
      * intuition.
      * intuition.
      
      * rewrite andb_true_iff in H.
        destruct H.
        apply leb_complete.
        destruct p1_2.
        destruct z. 
        -- intuition.
        -- repeat (rewrite andb_true_iff in H; destruct H).
          intuition.
        -- repeat (rewrite andb_true_iff in H; destruct H).
        intuition.
        -- repeat (rewrite andb_true_iff in H; destruct H).
        intuition.
        
        
      * intuition.
      * apply H0.
        destruct p1_2.
        destruct z. 
        -- intuition.
        -- repeat (rewrite andb_true_iff in H; destruct H).
          simpl.
          rewrite andb_true_iff.
          split; intuition.
        -- repeat (rewrite andb_true_iff in H; destruct H).
          simpl.
          rewrite andb_true_iff.
          split; intuition.
        -- repeat (rewrite andb_true_iff in H; destruct H).
          simpl.
          rewrite andb_true_iff.
          split; intuition.
       
      * destruct p1_2.
        destruct z.
        intuition.
        destruct n0.
        intuition.
        repeat (rewrite andb_true_iff in H; destruct H).
        apply leb_complete.
        intuition.
        repeat (rewrite andb_true_iff in H; destruct H).
        apply leb_complete.
        intuition.
        repeat (rewrite andb_true_iff in H; destruct H).
        apply leb_complete.
        intuition.

      
      * intuition.
      * apply H0.
        destruct p1_2.
        destruct z. 
        -- intuition.
        -- repeat (rewrite andb_true_iff in H; destruct H).
          simpl.
          rewrite andb_true_iff.
          split; intuition.
        -- repeat (rewrite andb_true_iff in H; destruct H).
          simpl.
          rewrite andb_true_iff.
          split; intuition.
        -- repeat (rewrite andb_true_iff in H; destruct H).
          simpl.
          rewrite andb_true_iff.
          split; intuition.

    + intuition. 
      simpl in H.
      rewrite andb_true_iff in H.
      destruct H.
      econstructor. 
      -- split. 
        ++ apply leb_complete. 
          destruct p1_2.
          destruct z.
          1: intuition.
          1-3: repeat (rewrite andb_true_iff in H; destruct H); destruct n0; intuition. 
        ++ apply leb_complete. 
        destruct p2_2.
        destruct z.
          1: intuition.
          1-3: repeat (rewrite andb_true_iff in H6; destruct H6); destruct n0; intuition. 
      
      -- split.
        ++ apply H0.
          simpl.
          destruct p1_2.
          destruct z.
          1: intuition.
          1-3: repeat (rewrite andb_true_iff in H; destruct H); destruct n0; intuition. 
        ++ apply H2.
          simpl.
          destruct p2_2.
          destruct z.
          1: intuition.
          1-3: repeat (rewrite andb_true_iff in H6; destruct H6); destruct n0; intuition.
  
  - intuition.
    induction H.
    + intuition.  
    + simpl.
      destruct y. 
      * intuition.
      * intuition.
      * intuition.
    + 
    simpl.
    induction x; intuition.
    
      * rewrite andb_true_iff.
        split.
        -- induction q. 
          destruct z.
          inversion H5; intuition.
          ++ destruct j.
            ** intuition.
            ** repeat (rewrite andb_true_iff; split).
              apply leb_correct; intuition.
              simpl in IHvalid_poly.
              repeat (rewrite andb_true_iff in IHvalid_poly; destruct IHvalid_poly).
              assumption.
              simpl in IHvalid_poly.
              repeat (rewrite andb_true_iff in IHvalid_poly; destruct IHvalid_poly).
              assumption.
          ++  destruct j.
            ** intuition.
            ** repeat (rewrite andb_true_iff; split).
              apply leb_correct; intuition.
              simpl in IHvalid_poly.
              repeat (rewrite andb_true_iff in IHvalid_poly; destruct IHvalid_poly).
              assumption.
              simpl in IHvalid_poly.
              repeat (rewrite andb_true_iff in IHvalid_poly; destruct IHvalid_poly).
              assumption.
          ++ destruct j.
            ** intuition.
            ** repeat (rewrite andb_true_iff; split).
              apply leb_correct; intuition.
              simpl in IHvalid_poly.
              repeat (rewrite andb_true_iff in IHvalid_poly; destruct IHvalid_poly).
              assumption.
              simpl in IHvalid_poly.
              repeat (rewrite andb_true_iff in IHvalid_poly; destruct IHvalid_poly).
              assumption.
            
        --  trivial.
      * rewrite andb_true_iff.
      split.
      -- induction q. 
        destruct z.
        inversion H5; intuition.
        ++ destruct j.
          ** intuition.
          ** repeat (rewrite andb_true_iff; split).
            apply leb_correct; intuition.
            simpl in IHvalid_poly.
            repeat (rewrite andb_true_iff in IHvalid_poly; destruct IHvalid_poly).
            assumption.
            simpl in IHvalid_poly.
            repeat (rewrite andb_true_iff in IHvalid_poly; destruct IHvalid_poly).
            assumption.
        ++  destruct j.
          ** intuition.
          ** repeat (rewrite andb_true_iff; split).
            apply leb_correct; intuition.
            simpl in IHvalid_poly.
            repeat (rewrite andb_true_iff in IHvalid_poly; destruct IHvalid_poly).
            assumption.
            simpl in IHvalid_poly.
            repeat (rewrite andb_true_iff in IHvalid_poly; destruct IHvalid_poly).
            assumption.
        ++ destruct j.
          ** intuition.
          ** repeat (rewrite andb_true_iff; split).
            apply leb_correct; intuition.
            simpl in IHvalid_poly.
            repeat (rewrite andb_true_iff in IHvalid_poly; destruct IHvalid_poly).
            assumption.
            simpl in IHvalid_poly.
            repeat (rewrite andb_true_iff in IHvalid_poly; destruct IHvalid_poly).
            assumption.
          
      --  trivial.
    + simpl.
      induction q.
      * destruct z.  
          
          inversion H4; intuition.
          ++ repeat (rewrite andb_true_iff; split).
              apply leb_correct; intuition.
              simpl in IHvalid_poly.
              repeat (rewrite andb_true_iff in IHvalid_poly; destruct IHvalid_poly).
              assumption.
              simpl in IHvalid_poly.
              repeat (rewrite andb_true_iff in IHvalid_poly; destruct IHvalid_poly).
              assumption.
          ++ repeat (rewrite andb_true_iff; split).
              apply leb_correct; intuition.
              simpl in IHvalid_poly.
              repeat (rewrite andb_true_iff in IHvalid_poly; destruct IHvalid_poly).
              assumption.
              simpl in IHvalid_poly.
              repeat (rewrite andb_true_iff in IHvalid_poly; destruct IHvalid_poly).
              assumption.
          
      * repeat (rewrite andb_true_iff; split).
      -- destruct j.
          **  apply leb_correct; intuition.
          **  apply leb_correct; intuition.
      -- simpl in IHvalid_poly. repeat (rewrite andb_true_iff in IHvalid_poly; destruct IHvalid_poly).
        assumption.
      --  simpl in IHvalid_poly. repeat (rewrite andb_true_iff in IHvalid_poly; destruct IHvalid_poly).
      assumption.
    
    +   admit.
Admitted.
    
Record valid_pol : Type :=
  { VP_value : poly ;
  VP_prop : valid_bool VP_value = true }.

Lemma leibniz (p q : valid_pol) : VP_value p = VP_value q -> p = q.
Proof.
  Print eq_rect.
  
  intro.
  induction p,q.
  simpl in H.
  
  eapply refl_equal.
  rewrite H.  
  unfold VP_value in H.
  eapply eq_rect in H.
