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
(* |Poly p j (Cst 0) => False *)
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
	valid_poly (Poly (Poly p' j' q') i (Poly p j q))
.

Fixpoint valid_b (pol:poly) : bool := 
match pol with 
|Cst _ => true
|Poly p i q => 
  match p,q with 
| _, (Cst 0) => false 
| (Cst _), (Cst _) => true 
| (Poly p1 j1 q1), (Cst _) => 
	Nat.ltb i j1 
  && valid_b p 
| (Cst _),  (Poly p2 j2 q2) => 
	Nat.leb i j2 
  && valid_b q 
|(Poly p1 j1 q1),  (Poly p2 j2 q2) => 
  Nat.leb i j1 && Nat.ltb i j2 
  && valid_b p 
  && valid_b q
  end 
end.

Lemma equivalence (p:poly) : valid_b p = true <-> valid_poly p.
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
    apply IHp2 in H4.
    rewrite <- H0 in IHp1.
    apply IHp1 in H5.
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

Lemma equivalence (p:poly) : valid_b p = true <-> valid_poly p.
Proof.
  unfold iff.
  induction p; split; intros.
  - econstructor.
  - simpl. trivial.
  - induction p1,p2.
    + econstructor.
      simpl in H.
      unfold "<>".
      intro.
      rewrite H0 in H.
      intuition. 
    + simpl in H.
      intuition.
      rewrite andb_true_iff in H.
      destruct H. 
      econstructor.
      * apply leb_complete.
        assumption.
      * intuition.
    + intuition.
      simpl in H.
      destruct z; econstructor.
      * intuition. 
      * intuition.
      * intuition.
      
      * rewrite andb_true_iff in H.
        destruct H.
        apply leb_complete.
        intuition.
      * intuition.
      * rewrite andb_true_iff in H.
        destruct H.
        intuition.
      * rewrite andb_true_iff in H.
      destruct H.
      apply leb_complete.
      intuition.
      * intuition.
      * 
       rewrite andb_true_iff in H.
        destruct H.
        intuition.
    + intuition.
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
  - intuition.
    destruct H.
    + intuition.  
    + simpl.
      destruct y. 
      * intuition.
      * intuition.
      * intuition.
    + 
      destruct x; intuition.
      * 
      simpl. rewrite andb_true_iff.
                   
      split.
        -- apply leb_correct.
          intuition.
        --  
        induction p,q.
        
        destruct z0; intuition.
     
     induction p1,p2.   
        admit.
        admit.
        admit.
        admit.
      * admit.
    + admit.
    + admit.
   
Admitted.
          

      





      Search ( _ <=? _ = true -> _ <= _).


(* Fixpoint valid_b (pol:poly) : bool := 
match pol with 
|Cst _ => true
|Poly p i (Cst 0) => false
|Poly (Cst _) i (Cst _) => true 
|Poly (Poly p j q) i (Cst _) => 
	Nat.leb i j 
  && valid_b (Poly p j q) 
|Poly (Cst _) i (Poly p' j' q') => 
	Nat.ltb i j' 
  && valid_b (Poly p' j' q') 
|Poly (Poly p j q) i (Poly p' j' q') => 
  Nat.leb i j && Nat.ltb i j' 
  && valid_b (Poly p j q) 
  && valid_b (Poly p' j' q') 
end. *)

Definition p1 := (Poly (Cst 0) 2 (Cst 1)).

Eval compute in (valid_b p1 0).

Lemma equivalence (p:poly) : valid_b p 0 = true <-> valid_poly p.
Proof.
  induction p; unfold iff; split;intro.
	- constructor.
  - simpl; reflexivity.
  - induction p2,p3; simpl in *.
    + econstructor. 
    + econstructor.
      * destruct p3_2.
        -- destruct z0.
          ++ intuition.
          ++ intuition.
            unfold ">=".
            admit.
          ++ 
          

Admitted.

