Require Import ZArith Bool.

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
  repeat let H' := fresh H in apply andb_true_iff in H as [H H'].

Ltac andb_split := 
  repeat (apply andb_true_iff; split).

Definition option_dec {A}(n: option A): {n' | n = Some n'} + {n = None}.
  destruct n; eauto.
Defined.

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


Lemma valid_b_tr (p q : poly) (z:Z) (n n0:nat) : 
  valid_b (Poly (Cst z) n (Poly p n0 q)) = true -> valid_b (Poly (Cst z) n q) = true.
Proof.
  intro.
  simpl in H.
  andb_destr H.
  induction p; induction q.
  - simpl; assumption.
  - andb_destr H0.
    simpl in H1.
    simpl.
    andb_split.
    Search (_ <=? _ -> _ <=? _ -> _ <=? _ ).
    apply leb_iff in H.
    apply leb_iff in H0.
    apply leb_iff.
    eapply le_trans with n0; assumption.
    assumption.
  - simpl. destruct z0; intuition.
  - andb_destr H0.
    simpl in H1.
    simpl.
    andb_split.
    apply leb_iff in H.
    apply leb_iff in H3.
    apply leb_iff.
    eapply le_trans with n0; assumption.
    assumption.
Qed.

Lemma poly_equivalence (p:poly) : valid_b p = true <-> valid_poly p.
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
      andb_destr H.
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
      
      -- andb_destr H.
        apply leb_complete.
        intuition.
      -- intuition.
      -- andb_destr H.
        intuition.
      -- andb_destr H.
      apply leb_complete.
      intuition.
      -- intuition.
      -- andb_destr H.
         intuition.
    * intuition.
      simpl in H.
      andb_destr H.
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
      andb_split.
      apply leb_correct; intuition.
      assumption.
      andb_split.
      apply leb_correct; intuition.
      assumption.



      -- rewrite <- H0 in IHp1.
      apply IHp1 in H5.
      simpl.
      simpl in H5.
      induction p; intuition.
      andb_split.
      apply leb_correct; intuition.
      assumption.
      andb_split.
      apply leb_correct; intuition.
      assumption.
  * rewrite <- H3 in IHp2.
    apply IHp2 in H4.
    simpl.
    simpl in H4. 
    andb_split.
    apply leb_correct; intuition.
    induction p; intuition.
  * destruct H4.

    (* rewrite <- H3 in IHp2.
    apply IHp2 in H5. *)

    rewrite <- H0 in IHp1.
    apply IHp1 in H4.
      simpl.
      simpl in H4.
      
      
      repeat (andb_split; try (apply leb_correct); intuition).
      
      rewrite <- H3 in IHp2.
      apply IHp2 in H5.
      simpl in H5.
      assumption.
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

  (* Set Implicit Arguments. *)
  Let comp [A] [x y y':A] (eq1:x = y) (eq2:x = y') : y = y' :=
    eq_ind _ (fun a => a = y') eq2 _ eq1.
  Print comp.

  Let trans_sym_eq [A] (x y:A) (u:x = y) : comp u u = eq_refl y.
  Proof.
    case u; trivial.
  Qed.

  Check trans_sym_eq.

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

Require Import List.
Import ListNotations.

Definition monoid : Type := list nat.

Fixpoint get_coefficient_ (pol: poly) (m:monoid) := 
  match pol with 
  | Cst z => if (forallb (fun (k:nat) (v:nat) => v =? 0%nat ) m) then z else 0%Z 
  | Poly p i q => 
    match find i m with 
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

Lemma for_all_add_add (m:monoid) (n0 n1 i: nat) :  P.for_all (fun _ v : nat => (v =? 0)%nat) (add i n1 (add i n0 m)) = P.for_all (fun _ v : nat => (v =? 0)%nat) (add i n1 m).
Proof.
  (* revert i.
  revert n1.
  revert n0. *)
  unfold P.for_all.
  erewrite P.fold_Equal with (m2:= add i n1 m).
  - reflexivity.
  - intuition.
  - intuition.
  - unfold P.transpose_neqkey; intros; destruct e,e'; intuition.
  - unfold Equal; intros.
    elim (Nat.eq_dec y i); intros.
    * rewrite a in *.
          rewrite F.add_eq_o; [|reflexivity].
          rewrite F.add_eq_o; [|reflexivity].
          reflexivity.
    * rewrite F.add_neq_o; [|intuition].
      rewrite F.add_neq_o; [|intuition].
      rewrite F.add_neq_o; [|intuition].
      reflexivity. 
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
    + specialize (H k e). rewrite a0 in H0. rewrite F.remove_mapsto_iff in H0. destruct H0. specialize (H0 eq_refl). contradiction. 
    + specialize (H k e). rewrite F.remove_mapsto_iff in H0.  destruct H0. specialize (H H2). rewrite H. assumption.
Qed.

Lemma for_all_add_0  (m:monoid) (i:nat) : P.for_all (fun _ v : nat => v =? 0) m = true 
  -> P.for_all (fun _ v : nat => v =? 0) (add i 0 m) = true.
Proof.
  intros.
  unfold P.for_all in *.
  rewrite P.fold_Equal with (m2:= add i 0 (NatMap.remove i m)).
  - rewrite P.fold_add.
    + simpl.
      elim (F.In_dec m i); intro.
      * rewrite F.mem_in_iff in a.
        assert (aaa: mem (elt:=nat) i (NatMap.remove i m) = false).
        apply F.remove_eq_b; apply eq_refl.
        rewrite <- F.not_mem_in_iff in aaa.
        rewrite <- F.mem_in_iff in a.
        specialize H as H'.
        apply for_all_remove.
        assumption.
      * 
        specialize H as H'. 
        apply for_all_remove.
        assumption.
    + intuition.
    + intuition.
    + unfold P.transpose_neqkey. 
      intuition.
      destruct e,e'; intuition.
    + rewrite F.not_mem_in_iff.
      rewrite F.remove_eq_b; reflexivity.
      
  - intuition.
  - intuition.
  - unfold P.transpose_neqkey.
    intuition.
    destruct e,e'; intuition.
  - unfold Equal.
    intros.
    elim (Nat.eq_dec i y); intros.
    + rewrite F.add_eq_o; [|assumption].
      rewrite F.add_eq_o; [|assumption]. 
      reflexivity.
    + rewrite F.add_neq_o; [|assumption].
      rewrite F.add_neq_o; [|assumption]. 
      rewrite F.remove_neq_o; [|assumption].
      reflexivity.
Qed.

Lemma for_all_add_S  (m:monoid) (i n:nat) :  P.for_all (fun _ v : nat => v =? 0) (add i (S n) m) = false.
Proof.
  unfold P.for_all.
  rewrite P.fold_Equal with (m2:= add i (S n) (NatMap.remove i m)).
  - rewrite P.fold_add.
    + simpl.
      reflexivity.
    + intuition.
    + intuition.
    + unfold P.transpose_neqkey. 
      intuition.
      destruct e,e'; intuition.
    + rewrite F.remove_in_iff.
      intro. 
      destruct H.
      specialize (H eq_refl).
      contradiction.
  - intuition.
  - intuition.
  - unfold P.transpose_neqkey.
    intuition.
    destruct e,e'; intuition.
  - unfold Equal.
    intros.
    elim (Nat.eq_dec i y); intros.
    + rewrite F.add_eq_o; [|assumption].
      rewrite F.add_eq_o; [|assumption]. 
      reflexivity.
    + rewrite F.add_neq_o; [|assumption].
      rewrite F.add_neq_o; [|assumption]. 
      rewrite F.remove_neq_o; [|assumption].
      reflexivity.
Qed.

Lemma get_coeff_add_add (i x y :nat) (m:monoid)  (p:poly) : valid_b p = true -> get_coefficient_ p (add i x m) = get_coefficient_ p (add i x (add i y m)).
Proof.
  intro.
  revert y.
  revert x.
  revert m.
  induction p.
  - simpl. intros.
    destruct x; rewrite for_all_add_add; reflexivity.
  - apply valid_b_more in H; destruct H.
    specialize (IHp1 H).
    specialize (IHp2 H0).
    simpl in *.
    intros.
    rewrite <- (IHp1 m x y).
    elim (Nat.eq_dec i n); intro.
    + rewrite a in *.
      rewrite F.add_eq_o; [|reflexivity].
      rewrite F.add_eq_o; [|reflexivity].
      destruct x.
      * reflexivity.
      * simpl.
        rewrite Nat.sub_0_r.
        rewrite <- (IHp2 (add n y m) x (S x)).
        rewrite <- (IHp2 (m) x (S x)).
        rewrite <- (IHp2 (m) x y).
        reflexivity.
    + rewrite F.add_neq_o; [|assumption].
      rewrite F.add_neq_o; [|assumption].
      rewrite F.add_neq_o; [|assumption].
      
      destruct (NatMap.find (elt:=nat) n m ); [|reflexivity].
      destruct n0.
      * reflexivity.
      * induction p3.
        -- simpl.
        rewrite Nat.sub_0_r.
        destruct n0.
Admitted.


Lemma for_all_exist_pos  (m:monoid) : (exists (n' r:nat), NatMap.find n' m = Some r /\ r <> 0) ->  P.for_all (fun _ v : nat => v =? 0) m = false.
Proof.
  intro.
  destruct H.
  destruct H.
  destruct H.
  unfold P.for_all.
  (* rewrite <- F.find_mapsto_iff in H. *)
  
  rewrite P.fold_Equal with  (m2:= add x x0 (NatMap.remove x m)).
  - rewrite P.fold_add.
    destruct x0.
    + unfold not in H0.
      specialize (H0 eq_refl); contradiction.
    + Search (S _ > 0).
      unfold "=?".
      trivial.
    + intuition.
    + intuition.
    + unfold P.transpose_neqkey. 
      intuition.
      destruct e,e'; intuition.
    + rewrite F.remove_in_iff.
      intro. 
      destruct H1.
      specialize (H1 eq_refl).
      contradiction.
    
  - intuition.
  - intuition.
  - unfold P.transpose_neqkey.
    intuition.
    destruct e,e'; intuition.
  - unfold Equal.
    intros.
    elim (Nat.eq_dec x y); intros.
    + rewrite F.add_eq_o. rewrite <- a. 
      assumption.
      assumption.
    + rewrite F.add_neq_o; [|assumption]. 
      rewrite F.remove_neq_o; [|assumption].
      reflexivity.
Qed.

Lemma coeffNot0 (p q : poly) (n:nat) : valid_b (Poly p n q) = true -> (exists (m : monoid), get_coefficient_ (Poly p n q) m <> 0%Z /\ exists (n' r:nat), NatMap.find n' m = Some r /\ r <> 0) .
Proof.
  intro valid.
  induction p; induction q.
  - elim (Z.eq_dec (z+z0) 0); intro.
    + elim (Z.eq_dec (z) 0); intro.
      * rewrite a0 in a. 
        simpl in a.
        unfold valid_b in valid.
        rewrite a in valid.
        inversion valid.
      * (* rewrite Zeq_plus_swap in a. *)
      exists (add n 1 empty_mono).
        simpl.
        split.
        -- rewrite F.add_eq_o; [|trivial].
        simpl.
        rewrite for_all_add_add.
        unfold P.for_all; rewrite P.fold_add; simpl; intuition.
          ++ unfold P.transpose_neqkey.
            intros. destruct e,e'; intuition.
          ++ rewrite F.empty_in_iff in H. contradiction.
        -- exists n. exists 1. 
          rewrite F.add_eq_o; split; intuition.
    + exists (add n 1 empty_mono).
      split.
      * simpl. 
        rewrite F.add_eq_o; [|trivial].
        simpl.
        rewrite for_all_add_add.
        elim (Z.eq_dec z0 0); intro.
        -- rewrite a in valid. 
          inversion valid.
        -- rewrite for_all_add_0.
          assumption.
          unfold P.for_all.
          unfold empty_mono.
          rewrite P.fold_Empty; intuition.
          apply empty_1.
      * exists n. exists 1.
      rewrite F.add_eq_o; split; intuition.
  - specialize valid as valid'.
    apply valid_b_tr in valid.
    specialize (IHq2 valid).
    destruct IHq2.
    destruct H.
    (* destruct H0.
    destruct H0.
    destruct H0. *)
    
    elim (option_dec (NatMap.find n x)); intro. 
    (* elim (Z.eq_dec z 0); intro. *)
    +
     (* rewrite a in *. *)
      destruct a.
      
      elim (Nat.eq_dec n0 n); intro.
      * rewrite a in *.
        eelim (Z.eq_dec (get_coefficient_ q1 (add n ( x0) x)) 0); intro.
        --  exists (add n ((S x0)) x).
              
              specialize valid' as valid2.
              split.
              simpl.
              rewrite F.add_eq_o; [|reflexivity].
              rewrite for_all_add_S.
              simpl.
              rewrite F.add_eq_o; [|reflexivity].
              simpl.
                
              apply valid_b_more in valid'; destruct valid' as (valid3 & valid4).
              apply valid_b_more in valid4; destruct valid4 as (valid5 & valid6). 
              
              rewrite <- get_coeff_add_add; [|assumption].
              rewrite <- get_coeff_add_add; [|assumption].
              rewrite <- get_coeff_add_add; [|assumption].
              rewrite Nat.sub_0_r.
              rewrite a0.
              simpl.
              specialize H as H'.
              simpl in H.
              rewrite e in H.
              destruct x0.
              ++ apply for_all_exist_pos in H0.
                rewrite H0 in H.
                assumption.
              ++ simpl.
                rewrite Nat.sub_0_r.
                simpl in H.
                rewrite Nat.sub_0_r in H.
                apply for_all_exist_pos in H0.
                rewrite H0 in H.
                assumption.
              ++ exists n. 
                exists (S x0).
                split.
                rewrite F.add_eq_o; reflexivity.
                intuition.

-- 
  specialize valid' as valid''.
  apply valid_b_more in valid'; destruct valid' as (valid3 & valid4).
  apply valid_b_more in valid4; destruct valid4 as (valid5 & valid6). 
  
   destruct q1.   
      ++ 
        elim (Nat.eq_dec x0 0); intro.
        ** rewrite a0 in *.
          exists (add n 1 (empty_mono)).   
          simpl.
          rewrite F.add_eq_o.
          rewrite F.add_eq_o.
          simpl.
          rewrite for_all_add_add. 
          rewrite for_all_add_0. 
          split.
          simpl in b.
          destruct (P.for_all (fun _ v : nat => v =? 0) (add n 0 x)); [assumption|].
          specialize (b eq_refl). contradiction.

          exists n.
          exists 1.
          rewrite F.add_eq_o; intuition.
          unfold P.for_all.
          rewrite P.fold_Empty; intuition.
          apply empty_1.
          reflexivity.
          reflexivity.
        
        ** exists (add n ((S x0)) x).
          simpl.
          rewrite F.add_eq_o; [|reflexivity].
          simpl.
          
          rewrite for_all_add_S.
          simpl.
          split.
          rewrite F.add_eq_o; [|reflexivity].
          simpl.
          rewrite Nat.sub_0_r.
          destruct x0.
          --- specialize (b0 eq_refl). contradiction.
          --- rewrite for_all_add_S. simpl. 
            rewrite <- get_coeff_add_add.
            rewrite <- get_coeff_add_add.
            simpl in H.
            rewrite e in H.
            unfold P.for_all in H.
            rewrite P.fold_Equal with (m2:= add n (S x0) (NatMap.remove n x)) in H.
            
            rewrite P.fold_add in H.
            simpl in H.
            assumption.
            intuition.
            intuition.
            unfold P.transpose_neqkey.
            intros.
            destruct e0,e'; intuition.
            rewrite F.not_find_in_iff.
            rewrite F.remove_eq_o.
            reflexivity.
            reflexivity.
            intuition.
            intuition.
            unfold P.transpose_neqkey.
            intros.
            destruct e0,e'; intuition.
            unfold Equal.
            intros.
            elim (Nat.eq_dec n y); intro.
            +++ rewrite a0 in *.
              rewrite F.add_eq_o.
              assumption.
              reflexivity.
            +++ rewrite F.add_neq_o; [|assumption].
                rewrite F.remove_neq_o; intuition.
            +++ 
            assumption.
            +++ 
            assumption.
          --- exists n.
          exists (S x0).
          split.
          rewrite F.add_eq_o; reflexivity.
          intuition.
      ++ elim (Nat.eq_dec n n1); intro.
        ** simpl in valid''. andb_destr valid''.
          destruct q2.
          destruct z0.
          inversion valid''0. 
          andb_destr valid''0.
          rewrite a0 in valid''0.
          rewrite Nat.ltb_irrefl in valid''0.
          inversion valid''0.
          
          andb_destr valid''0.
          rewrite a0 in valid''0.
          rewrite Nat.ltb_irrefl in valid''0.
          inversion valid''0.

          andb_destr valid''0.
          rewrite a0 in valid''0.
          rewrite Nat.ltb_irrefl in valid''0.
          inversion valid''0.

        ** eelim (option_dec (NatMap.find (elt:=nat) n1 x)  ); intro.
          elim (Z.eq_dec ((get_coefficient_ (Poly (Cst z) n q2) x) + (get_coefficient_ (Poly q1_1 n1 q1_2) (add n x0 x))) 0); intro.
          --- destruct a0.
            elim (Z.eq_dec z 0); intro.
            +++ rewrite a0 in *.
            elim (Nat.eq_dec x0 0); intro.
            (* elim (Nat.eq_dec x1 0); intro. *)
            
            rewrite a2 in *.
            (* rewrite a3 in *. *)
            *** 
            exists ( x).
            split.
            simpl.
            rewrite e.
            simpl in a1.
            rewrite e in a1.
            rewrite for_all_exist_pos; [|assumption].
            
            simpl in a1.
            rewrite F.add_neq_o in a1; [|assumption].

            rewrite e0 in a1.
            destruct x1.
            simpl in b.
            rewrite F.add_neq_o in b; [|assumption].
            rewrite e0 in b.
            rewrite for_all_exist_pos in a1; [|assumption]; simpl in a1.
            rewrite a1 in b.
            specialize (b eq_refl); inversion b.

            simpl in b.
            rewrite F.add_neq_o in b; [|assumption].
            rewrite e0 in b.
            rewrite for_all_exist_pos in a1; [|assumption]; simpl in a1.
            simpl in b.
            rewrite a1 in b.
            specialize (b eq_refl); inversion b.

            assumption.
            
            *** elim (Nat.eq_dec x1 0); intro.
              ---- rewrite a2 in *.
                  simpl in b.
                  rewrite F.add_neq_o in b; [|assumption].
                  rewrite e0 in b.
                  simpl in a1.
                  rewrite e in a1.
                  rewrite F.add_neq_o in a1; [|assumption].
                  rewrite e0 in a1.
                  destruct x0.
                  specialize (b1 eq_refl); inversion b1.

                  rewrite for_all_exist_pos in a1; [|assumption]; simpl in a1.
            
            simpl in a1.
            rewrite Nat.sub_0_r in a1.
            exists (add n1 1 x).
            split.
            simpl.
             rewrite F.add_neq_o.
             rewrite e.
             simpl.
              rewrite for_all_add_S. simpl.
              rewrite Nat.sub_0_r.
              rewrite F.add_eq_o.
              destruct x0.
            1-2:  rewrite F.add_neq_o; [|assumption].
            1-2:  rewrite F.add_eq_o; [|reflexivity].
            1-2:  simpl.
            

  Admitted.















  (* apply P.fold_rec.
  
  induction fold.
rewrite <- P.for_all_iff. *)


Lemma coeff_map_add' (n n' i: nat) (p:poly) (m:monoid) : 
get_coefficient_ p m = get_coefficient_ p (add i (S n) (add i n' m)) 
-> 
get_coefficient_  p (add i n m) = get_coefficient_ p (add i n (add i (S n) (add i n' m))) .
Proof.
  intros.
  induction p.
  - simpl.
    unfold P.for_all.
    rewrite P.fold_Equal with (m2:=(add i n (add i (S n) (add i n' m))) ); intuition.
    unfold P.transpose_neqkey; intros; destruct e,e'; intuition.
    unfold Equal.
    intros.
    elim (Nat.eq_dec y i); intro.
    + rewrite F.add_eq_o; [|intuition].
      rewrite F.add_eq_o; [|intuition].
      reflexivity.
    + rewrite F.add_neq_o; [|intuition].
    rewrite F.add_neq_o; [|intuition].
    rewrite F.add_neq_o; [|intuition].
    rewrite F.add_neq_o; [|intuition].
    reflexivity.
  - simpl in H.
    simpl.
Admitted.  





(* Lemma coeff_map_add (p:poly) (m:monoid) (n n'  i: nat) : get_coefficient_ p (add i n m) = get_coefficient_ p (add i n (add i n' m)).
Proof.
  revert n.
  revert n'.
  revert i.
  revert m.
  induction p; intros.
  - simpl.
    unfold P.for_all.
      rewrite P.fold_Equal with (m1:=(add i n (add i n' m))) (m2:= add i n m).
      + reflexivity.
      + intuition.
      + intuition.
      + unfold P.transpose_neqkey. intros. destruct e,e'; intuition.
      + unfold Equal.
        intros.
        elim (Nat.eq_dec y i); intro.
        * rewrite a in *.
          rewrite F.add_eq_o; [|reflexivity].
          rewrite F.add_eq_o; [|reflexivity].
          reflexivity.
        * rewrite F.add_neq_o; [|intuition].
          rewrite F.add_neq_o; [|intuition].
          rewrite F.add_neq_o; [|intuition].
          reflexivity. 
  - simpl.
    rewrite <- IHp1.
    elim (Nat.eq_dec n i); intro.
    + rewrite a in *.
      rewrite F.add_eq_o ; [|intuition].
      rewrite F.add_eq_o; [|intuition].
      destruct n0; [reflexivity|].
      simpl.
      rewrite Nat.sub_0_r.
      rewrite <- IHp2 with (i:=i) (n':=S n0) (n:=n0) .
      rewrite <- IHp2 with (i:=i) (n':=S n0) (n:=n0) (m:= add i n' m).
      rewrite <- IHp2.
      reflexivity.
    + rewrite F.add_neq_o ; [|intuition].
      rewrite F.add_neq_o ; [|intuition].
      rewrite F.add_neq_o ; [|intuition].
      destruct (NatMap.find (elt:=nat) n m); [|reflexivity].
      destruct n1; [reflexivity|].
      simpl.
      rewrite Nat.sub_0_r.

      (* rewrite <- IHp2 with (i:=i) (n:=n1) (n':=n0) .
      rewrite <- IHp2 with (i:=i) (n':=S n0) (n:=n0) (m:= add i n' m).
      rewrite <- IHp2. *)
      
      induction p3.
      * simpl.
      unfold P.for_all.
      rewrite P.fold_Equal with (m1:= add n n1 (add i n0 m)) (m2:= add n n1 (NatMap.remove n (add i n0 m))) ; [intuition | intuition | intuition | unfold P.transpose_neqkey |  ].
      rewrite P.fold_Equal with (m1:= (add n n1 (add i n0 (add i n' m)))) (m2:= (add n n1 (NatMap.remove n (add i n0 (add i n' m)))))  ; [intuition | intuition | intuition | unfold P.transpose_neqkey |  ].
      -- simpl in *.
        
        unfold P.for_all in IHp2.
        (* assert (aaa: fold (fun (_ : key) (e : nat) (b0 : bool) => if (e =? 0)%nat then b0 else false)
        (add n n1 (NatMap.remove (elt:=nat) n (add i n0 m))) true = fold (fun (_ : key) (e : nat) (b0 : bool) => if (e =? 0)%nat then b0 else false)
        (add n n1 (NatMap.remove (elt:=nat) n (add i n0 (add i n' m)))) true). *)

        specialize (IHp2 m i n' n0) as IHp2'.
        
      rewrite P.fold_add with (k:=n); [intuition | intuition | intuition | unfold P.transpose_neqkey |  ].
      rewrite P.fold_add with (k:=n); [intuition | intuition | intuition | unfold P.transpose_neqkey |  ].
      (* rewrite P.fold_add; [intuition | intuition | intuition | unfold P.transpose_neqkey |  ].
      rewrite P.fold_add; [intuition | intuition | intuition | unfold P.transpose_neqkey |  ]. *)
      destruct n1; simpl; try intuition.
      ++ destruct z.
      destruct (( fold (fun (_ : key) (e : nat) (b : bool) => if e =? 0 then b else false) (add i n0 m) true)).
      ++ intros; destruct e,e'; intuition.
      ++ rewrite F.not_find_in_iff.
         rewrite F.remove_eq_o; reflexivity.
      ++ intros; destruct e,e'; intuition.
      ++ rewrite F.not_find_in_iff.
         rewrite F.remove_eq_o; reflexivity.
      -- intros; destruct e,e'; intuition.
      -- unfold Equal.
        intros.
        

      specialize (IHp2 m i n' 0) as IHp2'.
      simpl in IHp2'.
      unfold P.for_all in IHp2'. 
      rewrite P.fold_add in IHp2'; [intuition | intuition | intuition | unfold P.transpose_neqkey | ].
      simpl in IHp2'.
      destruct n'.
      simpl.
      reflexivity.
      simpl.
      intuition.              
      rewrite <- IHp2'.

      rewrite P.fold_add.

    eelim (option_dec (NatMap.find (elt:=nat) n (add i n0 (add i n' m)) ) ); intro.
    + destruct a.
      rewrite e.
Admitted. *)        


Lemma coeff_map_add (p:poly) (m:monoid) (n i: nat) : 
 NatMap.find (elt:=nat) i m = Some n ->  get_coefficient_ p m = get_coefficient_ p (add i n m).
Proof.
  revert n.
  revert i.
  revert m.
  
  induction p; intros.
  - simpl.
  
    unfold P.for_all.
    
    
     rewrite P.fold_Equal with (m1:=(add i n m)) (m2:=m).
      * reflexivity.
      * intuition.
      * intuition.
      * unfold P.transpose_neqkey. intros. destruct e,e'; intuition.
      * unfold Equal.
        intros.
        elim (Nat.eq_dec y i); intro.
        -- rewrite a in *.
          rewrite F.add_eq_o.
          rewrite H.
          reflexivity.
          reflexivity.
        -- rewrite F.add_neq_o.
          reflexivity.
          intuition.
  - simpl.
    specialize (IHp1 m i n0 H) as IHp1n0.
    specialize (IHp2 m i n0 H) as IHp2n0.

    (* specialize (IHp1 i n) as IHp1IN. *)

    elim (Nat.eq_dec n i); intro.
    -- rewrite a in *.
    rewrite F.add_eq_o; [|reflexivity].
    rewrite <- IHp1n0.
    rewrite H.
    destruct n0.
    reflexivity.
    simpl.
    rewrite Nat.sub_0_r.
    

    destruct p3.
    ++ simpl in IHp2.

Admitted.



Lemma all_coeff_eq (p q : valid_pol) : (forall (m : monoid), get_coefficient p m = get_coefficient q m) -> p = q.
Proof.
  unfold get_coefficient.
  destruct p,q.
  simpl.
  intro.
  apply leibniz.
  simpl.

  induction VP_value0; induction VP_value1.

  - specialize (H empty_mono). simpl in H. f_equal. assumption.
  - apply valid_b_more in VP_prop1 as validV.
    destruct validV as (validV1 & validV2).
    specialize (IHVP_value1_1 validV1).
    specialize (IHVP_value1_2 validV2).
    
    induction VP_value1_1. 
    
    + elim (Z.eq_dec z z0); intro.
      * rewrite <- a in IHVP_value1_1. 
        unfold VP_value in IHVP_value1_1.
        unfold VP_value in IHVP_value1_2.

        (*  *)
        rewrite <- a in *.
        elim (Z.eq_dec z 0); intro.
        -- rewrite a0 in *.
          assert (aaa : exists m, get_coefficient_ (Poly (Cst 0) n VP_value1_2) m <> 0%Z /\ exists (n' r:nat), NatMap.find n' m = Some r /\ r <> 0).
          eapply (coeffNot0 ).
          assumption.
          destruct aaa.
          specialize (H x).
          unfold get_coefficient_ at 1 in H.
          destruct (fold (fun (_ : key) (v : nat) (acc : bool) => acc && (v =? 0)) x true).
          unfold not in H0.
          rewrite <- H in H0.
          destruct H0.
          destruct (P.for_all (fun _ v : nat => v =? 0) x);specialize (H0 eq_refl);contradiction.

          unfold not in H0.
          rewrite <- H in H0.
          destruct H0.
          destruct (P.for_all (fun _ v : nat => v =? 0) x);specialize (H0 eq_refl);contradiction.

        -- specialize (H (add n 1 empty_mono)) as Hn1.
          simpl in Hn1.
          erewrite F.add_eq_o in Hn1; [|reflexivity].
          simpl in Hn1.
        
          destruct VP_value1_2.
        ++ elim (Z.eq_dec z1 0); intro.
          rewrite a0 in *.
          inversion VP_prop1.

          simpl in Hn1.
          unfold P.for_all in Hn1.
          erewrite P.fold_Equal with (m2:= add n 0 (empty nat)) in Hn1. 
          erewrite P.fold_add with (k:=n ) (e:=0) in Hn1; intuition; simpl in Hn1.
          rewrite <- Hn1 in VP_prop1. simpl in VP_prop1. inversion VP_prop1. (* z1 can't be 0%Z *) 
          unfold P.transpose_neqkey.
          intuition.
          
          destruct e,e'; simpl; reflexivity.
          
          intuition.
          intuition.
          unfold P.transpose_neqkey.
          intuition. destruct e,e'; simpl; reflexivity.
          unfold Equal.
          intuition.
          elim (Nat.eq_dec y n); intro.
          erewrite F.add_eq_o ; intuition.
          erewrite F.add_eq_o ; intuition.
          erewrite F.add_neq_o ; intuition.
          erewrite F.add_neq_o ; intuition.
          erewrite F.add_neq_o ; intuition.
        
        ++ 

        
        assert (aaa : exists m, get_coefficient_ (Poly VP_value1_2_1 n0 VP_value1_2_2) m <> 0%Z /\ exists (n' r:nat), NatMap.find n' m = Some r /\ r <> 0).
          eapply (coeffNot0 ).
          assumption.
        destruct aaa.

        specialize (H (add n (match NatMap.find n x with Some n' => n'+1 |_=> 1 end) ( x))) as exiN1.
        simpl in H0.

        elim (option_dec (NatMap.find (elt:=nat) n x)); intro.
  
        (* destruct (NatMap.find (elt:=nat) n x). *)
        (* elim (F.In_dec x n); intro. *)
        
        ** 
          specialize a0 as a1.
          (* rewrite F.in_find_iff in a0.  *)
          destruct a1.
          rewrite e in exiN1.
          (* destruct (NatMap.find (elt:=nat) n x); [|unfold not in a0; specialize (a0 eq_refl); contradiction]. *)
          
          simpl in exiN1.
          erewrite F.add_eq_o in exiN1; [|reflexivity].
          
          destruct x0.
          --- rewrite Nat.add_0_l in exiN1.
              specialize e as e'.
              (* eapply P.fold_rec_nodep in exiN1. *)
              elim (bool_dec (P.for_all (fun _ v : nat => v =? 0) (add n 1 x)) true); intro.
              rewrite P.for_all_iff in a1.
              specialize (a1 n 1).
              simpl in a1.
              rewrite F.add_mapsto_iff in a1.
              apply False_rect.
              Search (false=true).
              apply diff_false_true.
              apply a1.
              
              left.
              intuition.
              intuition.
              
              elim (bool_dec (P.for_all (fun _ v : nat => v =? 0) (add n 1 x)) false); intro.
              rewrite a1 in b0.
              rewrite a1 in exiN1.
              simpl in exiN1.
              (*  *)
              +++ elim (Nat.eq_dec n0 n); intro.
                *** rewrite F.add_eq_o in exiN1.
                    replace (add n 0 (add n 1 x)) with x in exiN1; [|admit].
                    rewrite a2 in H0.
                    rewrite e in H0.
                    unfold not in H0.
                    destruct H0.
                    rewrite Z.eq_sym_iff in exiN1.
                    specialize (H0 exiN1).
                    contradiction.
                    rewrite Nat.eq_sym_iff.
                    assumption.
                *** rewrite F.add_neq_o in exiN1.
                    rewrite F.add_neq_o in exiN1.
                    replace (add n 0 (add n 1 x)) with x in exiN1; [|admit].
                    unfold not in H0.
                    rewrite Z.eq_sym_iff in exiN1.
                    destruct H0.
                    specialize (H0 exiN1).
                    contradiction.
                    intuition.
                    intuition.
              +++ unfold not in b0,b1.
                  destruct ( P.for_all (fun _ v : nat => v =? 0) (add n 1 x)).
                  specialize (b0 eq_refl); contradiction.
                  specialize (b1 eq_refl); contradiction.
            
          --- simpl in exiN1. 
              rewrite Nat.sub_0_r in exiN1.
              rewrite Nat.add_1_r in exiN1.
              rewrite for_all_add_S in exiN1.
              simpl in exiN1.

              elim (Nat.eq_dec n0 n); intro.
                +++ rewrite F.add_eq_o in exiN1.
                    replace (add n (S x0) (add n (S (S x0)) x)) with x in exiN1; [|admit].
                    rewrite a1 in H0.
                    rewrite e in H0.
                    unfold not in H0.
                    rewrite <- a1 in H0.
                    rewrite Z.eq_sym_iff in exiN1.
                    destruct H0.
                    specialize (H0 exiN1).
                    contradiction.
                    rewrite Nat.eq_sym_iff.
                    assumption.
                +++ rewrite F.add_neq_o in exiN1.
                    rewrite F.add_neq_o in exiN1.
                    replace (add n (S x0) (add n (S (S x0)) x)) with x in exiN1; [|admit].
                    rewrite Z.eq_sym_iff in exiN1.
                    destruct H0.
                    specialize (H0 exiN1).
                    contradiction.
                    intro; unfold not in b0; rewrite Nat.eq_sym_iff in H1; specialize (b0 H1); contradiction. 
                    intro; unfold not in b0; rewrite Nat.eq_sym_iff in H1; specialize (b0 H1); contradiction.
          
        ** rewrite b0 in exiN1. 
        simpl in exiN1.
        rewrite for_all_add_S in exiN1.
        rewrite F.add_eq_o in exiN1.
        simpl in exiN1.
        rewrite Z.eq_sym_iff in exiN1.
        elim (Nat.eq_dec n0 n); intro.
        +++ rewrite F.add_eq_o in exiN1; [|rewrite Nat.eq_sym_iff; assumption].
            rewrite a0 in H0.
            rewrite b0 in H0.
            replace ((add n 0 (add n 1 x))) with x in exiN1; [|admit].
            unfold not in H0.
            destruct H0.
            specialize (H0 exiN1).
            contradiction.
        +++ rewrite F.add_neq_o in exiN1; [|rewrite Nat.eq_sym_iff; assumption].
            rewrite F.add_neq_o in exiN1; [|rewrite Nat.eq_sym_iff; assumption].
            
            replace (add n 0 (add n 1 x)) with ( x) in exiN1; [|admit].
            destruct H0.
            specialize (H0 exiN1).
            contradiction.
        +++ trivial.
    * specialize (H empty_mono).
      simpl in H.
      specialize (b H).
      contradiction.
  + assert (aaa : exists m, get_coefficient_ (Poly (Poly VP_value1_1_1 n0 VP_value1_1_2) n VP_value1_2)  m <> 0%Z /\ exists (n' r:nat), NatMap.find n' m = Some r /\ r <> 0).
    
    eapply (coeffNot0 ).
    assumption.
    destruct aaa.
    specialize (H x).
    unfold get_coefficient_ at 1 in H.
    destruct H0.
    specialize (for_all_exist_pos x H1).
    intro.
    rewrite H2 in H.
    unfold not in H0.
    rewrite Z.eq_sym_iff in H.
    specialize (H0 H).
    contradiction.
- admit. (* symmetric proof of the previous subgoal *)
- admit.
 Admitted.


(* 

  Require Import Program.

  Lemma valid_b_moreP (p q : poly) (i:nat) : 
    valid_b (Poly p i q) = true -> valid_b p = true.
  Proof.
    apply valid_b_more.
  Qed.

  Lemma valid_b_moreQ (p q : poly) (i:nat) : 
    valid_b (Poly p i q) = true -> valid_b q = true.
  Proof.
    apply valid_b_more.
  Qed.

  Require Import Program.

  Program Definition valid_b_poldec (pol : poly) (p q:poly) (i:nat) (pr : valid_b pol = true) (preq : pol = (Poly p i q))  := _ :
  valid_b (Poly p i q) = true.

  Fixpoint size (p:poly) := match p with 
  |Cst _ => 0
  |Poly p _ q => 1 + size p + size q
  end.

  Program Fixpoint poly_val (pol:valid_pol) (f : nat -> Z) {measure (size (VP_value pol))} : Z := 
    match VP_value pol as x0 return (VP_value pol = x0) -> Z with 
    | Cst z => fun (e: (VP_value pol) = (Cst z)) => z
    | Poly p i q => 
      fun (e: (VP_value pol) = Poly p i q) =>
      let pr := valid_b_poldec (VP_value pol) p q i (VP_prop pol) e in 
      let pr1 := valid_b_moreP p q i pr in 
      let pr2 := valid_b_moreQ p q i pr in 
      Z.add (poly_val {| VP_value := p ; VP_prop := pr1|} f) (Z.mul (f i) (poly_val {| VP_value := q ; VP_prop := pr2|}  f))
    end
    eq_refl.
  Next Obligation.
  rewrite e.
  unfold size.
  intuition.
  Defined.
  Next Obligation.
  rewrite e.
  unfold size.
  intuition.
  Defined.

  Check poly_val.

  Lemma val_coeff (p q : valid_pol) : (forall (f:nat -> Z), poly_val p f = poly_val q f) -> (forall (m: monoid ), get_coefficient p m = get_coefficient q m).
  Proof.
    intros.
    induction p,q.
    unfold poly_val in H.
    unfold poly_val_func in H.
    induction VP_value0,VP_value1.

    - 
  Admitted. 
*)

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
  destruct p,q.
  unfold get_coefficient.
  unfold VP_value.
  unfold poly_val in H.
  unfold VP_value in H.

  induction VP_value0; unfold poly_val in H; unfold VP_value in H.
  - induction VP_value1. unfold poly_val_ in H.
    + intuition.
      rewrite H0.
      reflexivity.dv
    + 
      apply valid_b_more in VP_prop1 as validV.
      destruct validV as (validV1 & validV2).
      specialize (IHVP_value1_1 validV1).
      specialize (IHVP_value1_2 validV2).

      unfold poly_val_ in H.
      fold poly_val_ in H.

      unfold poly_val_ in IHVP_value1_1.
      (* unfold get_coefficient_ in IHVP_value1_1. *)
      simpl in IHVP_value1_1.
      fold poly_val_ in IHVP_value1_1.
      (* fold get_coefficient_ in IHVP_value1_1. *)

      unfold get_coefficient_.
      fold get_coefficient_.

      
      
      case_eq (fold (fun (_ : key) (v : nat) (acc : bool) => acc && (v =? 0)) m true); intro.
      * 
        case_eq (NatMap.find (elt:=nat) n m); intros; simpl.
        -- destruct n0.
          rewrite H0 in IHVP_value1_1.
        apply IHVP_value1_1.
        
        intros.

        specialize (H f).

        unfold poly_val_ in H.

      
      destruct (NatMap.find (elt:=nat) n m).
      fold poly_val_ in H.
      unfold get_coefficient_.
      fold get_coefficient_.
    
  (* - 
    unfold get_coefficient_.
    destruct (fold (fun (_ : key) (v : nat) (acc : bool) => acc && (v =? 0)) m true).
    destruct (NatMap.find (elt:=nat) n m).
    fold get_coefficient_.
    simpl in H. *)
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

(* Eval compute in (eval_form (# 0 → # 0) valuation).
Eval compute in (eval_form (# 0 → # 1) valuation).
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
let v := read_term (impb (negb false) true) (@nil bool) in
idtac v.
Abort .


Definition cst_poly (z:Z) := {| VP_value := (Cst z); VP_prop := eq_refl |}.

Require Import Program.

Fixpoint length (p:poly) := 
  match p with 
  |Cst _ => 1 
  |Poly p _ q => 1 + length p + length q 
  end.

Program Fixpoint sum_poly_ (p q:poly) {measure (length p + length q) } := 
  match p,q with 
  |Cst z1, Cst z2 => Cst (Z.add z1 z2)
  |Poly p1 i q1, Cst z2 => 
    Poly (sum_poly_ p1 (Cst z2)) i q1
  |Cst z1, Poly p2 j q2 => 
  Poly (sum_poly_ p2 (Cst z1)) j q2
  |Poly p1 i q1, Poly p2 j q2 => 
    if i =? j 
    then Poly (sum_poly_ p1 p2) i (sum_poly_ q1 q2)
    else Poly (sum_poly_ p1 (Poly p2 j q2)) i q1
  end.
Next Obligation.
  simpl.
  intuition.
  Qed.
  Next Obligation.
  simpl.
  intuition.
  Qed.
  Next Obligation.
  simpl.
  intuition.
  Qed.
  Next Obligation.
  simpl.
  intuition.
  Qed.
  Next Obligation.
  simpl.
  intuition.
Defined.

Definition pol1 := (Poly (Cst 1%Z) 1 (Poly (Cst 1%Z) 2 (Cst 1%Z))).
Definition pol2 := (Poly (Cst 2%Z) 2 (Poly (Cst 2%Z) 3 (Cst 2%Z))).

Eval compute in (sum_poly_ pol1 pol2).

Program Definition sum_poly (p q:valid_pol) := {|VP_value := sum_poly_ (VP_value p) (VP_value q) ; VP_prop := _ |}.
Admit Obligations.



Program Fixpoint mul_poly_ (p q:poly) {measure (length p + length q) } := 
  match p with 
  |Cst z1 => 
    match q with 
    |Cst z2 => Cst (Z.mul z1 z2)
    |Poly p2 j q2 => Poly (mul_poly_ (Cst z1) p2 ) j (mul_poly_ (Cst z1) q2 )
    end 
  |Poly p1 i q1 => 
    match q with 
    | Cst z2 => Poly (mul_poly_ (Cst z2) p1) i (mul_poly_ (Cst z2) q1 )
    | Poly p2 j q2 => 
      match Nat.compare i j with 
      |Lt => Poly (mul_poly_ p1 (Poly p2 j q2)) i (mul_poly_ q1 (Poly p2 j q2))
      |Gt => Poly (mul_poly_ p2 (Poly p1 i q1)) j (mul_poly_ q2 (Poly p1 i q1))
      |Eq => Poly (mul_poly_ p1 p2) i (Poly (mul_poly_ p1 q2) j (mul_poly_ q1 q2)) 
      end
    end
  end.
Next Obligation.
  simpl.
  intuition.
  Qed.
  Next Obligation.
  simpl.
  intuition.
  Qed.
  Next Obligation.
  simpl.
  intuition.
  Qed.
  Next Obligation.
  simpl.
  intuition.
  Qed.
  Next Obligation.
  simpl.
  intuition.
  Qed.
  Next Obligation.
  simpl.
  intuition.
  Qed.
  Next Obligation.
  simpl.
  intuition.
  Qed.
  Next Obligation.
  simpl.
  intuition.
  Qed.
  Next Obligation.
  simpl.
  intuition.
  Qed.
  Next Obligation.
  simpl.
  intuition.
  Qed.
  Next Obligation.
  simpl.
  intuition.
Defined.


Lemma mul_eq (p q:poly) : mul_poly_ p q = 
match p with 
  |Cst z1 => 
    match q with 
    |Cst z2 => Cst (Z.mul z1 z2)
    |Poly p2 j q2 => Poly (mul_poly_ (Cst z1) p2 ) j (mul_poly_ (Cst z1) q2 )
    end 
  |Poly p1 i q1 => 
    match q with 
    | Cst z2 => Poly (mul_poly_ (Cst z2) p1) i (mul_poly_ (Cst z2) q1 )
    | Poly p2 j q2 => 
      match Nat.compare i j with 
      |Lt => Poly (mul_poly_ p1 (Poly p2 j q2)) i (mul_poly_ q1 (Poly p2 j q2))
      |Gt => Poly (mul_poly_ p2 (Poly p1 i q1)) j (mul_poly_ q2 (Poly p1 i q1))
      |Eq => Poly (mul_poly_ p1 p2) i (Poly (mul_poly_ p1 q2) j (mul_poly_ q1 q2)) 
      end
    end
  end.
Proof.
Admitted.

Eval compute in (mul_poly_ pol1 pol2).

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


Lemma mul_pol_1 : forall (p:poly),  (mul_poly_ (Cst 1) p)  = p .
Proof.
intros.
induction  p.
- simpl. destruct z; trivial.
- rewrite mul_eq. 
  simpl.
  rewrite IHp1.
  rewrite IHp2.
  reflexivity.
Qed. 

Lemma mul_pol_0 : forall (p:poly) (val:nat -> Z), Z.eq (poly_val_ (mul_poly_ (Cst 0) p) val)  0%Z .
Proof.
intros.
induction  p.
- simpl. intuition.
- rewrite mul_eq. 
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
- simpl. rewrite mul_eq. rewrite Z.mul_1_r. reflexivity.
- rewrite mul_eq.
  rewrite mul_pol_1.
  rewrite mul_pol_1.
  reflexivity.
Qed.


Lemma mul_pol_0_r : forall (p:poly) (val:nat -> Z), Z.eq (poly_val_ (mul_poly_ p (Cst 0)) val)  0%Z .
Proof.
intros.
induction  p.
- simpl. rewrite Z.mul_0_r. reflexivity.
- rewrite mul_eq.
  simpl.
  rewrite mul_pol_0.
  rewrite mul_pol_0.
  simpl.
  rewrite Z.mul_0_r.
  reflexivity.
Qed.

(* Goal  forall (val:nat->bool) (f1 f2:form), (poly_val (to_poly f1 val) (fun x : nat => if val x then 1 else 0) =? 1)%Z &&
(poly_val (to_poly f2 val) (fun x : nat => if val x then 1 else 0) =? 1)%Z =
(poly_val (mul_poly (to_poly f1 val) (to_poly f2 val))
   (fun x : nat => if val x then 1 else 0) =? 1)%Z.

  intros.
  
  induction f1; induction f2.
  - simpl. trivial.
  - simpl. trivial.
  - simpl. destruct (val n); intuition.
  - simpl in *.
    unfold poly_val.
    simpl.
    rewrite mul_pol_1.
    
    
    unfold poly_val in *.
    simpl in *.
    
    induction ((mul_poly_ (VP_value (to_poly f2_1 val)) (VP_value (to_poly f2_2 val)))).
  
    + simpl. destruct z; intuition.
    + unfold poly_val_. destruct (val n). fold poly_val_.  
      
      * rewrite Z.mul_1_l.


        simpl in IHp1. rewrite IHp1.
    simpl.
    fold mul_poly.
    

   rewrite IHf2_1.
Abort *)


Hint Rewrite Z.mul_0_r : core.

Require Import Lia.

Definition z_of_bool := (fun x : bool => if x then 1%Z else 0%Z).

(* Lemma mul_poly_comm (p q : valid_pol) : (mul_poly p q) = (mul_poly q p).
Proof.
  destruct p as ( p & ? ).
  destruct q as ( q & ? ).
  unfold mul_poly.
  apply leibniz. 
  simpl.
  induction p.
  - induction q. 
    + rewrite mul_eq. 
      rewrite mul_eq.
      rewrite Z.mul_comm.
      reflexivity.
    + apply valid_b_more in VP_prop1. destruct VP_prop1 as (validq1 & validq2).
    specialize (IHq1 validq1).
    specialize (IHq2 validq2).
    rewrite mul_eq. 
    rewrite IHq1.
    rewrite IHq2.
    rewrite mul_eq.
    rewrite mul_eq.
    rewrite mul_eq.
    rewrite mul_eq.
    rewrite mul_eq.
    destruct q1,q2; intuition.
    * rewrite Z.mul_comm.
    rewrite Z.mul_comm with (n:= z1).
    reflexivity.

    * rewrite Z.mul_comm. reflexivity.
    * rewrite Z.mul_comm. reflexivity.
  - apply valid_b_more in VP_prop0. destruct VP_prop0 as (validp1 & validp2).
    specialize (IHp1 validp1).
    specialize (IHp2 validp2).
    induction q.
    rewrite mul_eq. 
    rewrite mul_eq.
    rewrite mul_eq.
    rewrite mul_eq.
    rewrite mul_eq.
    rewrite mul_eq.
    induction p2; induction p3; intuition. 
    apply valid_b_more in VP_prop1. destruct VP_prop1 as (validq1 & validq2).
    specialize (IHq1 validq1).
    specialize (IHq2 validq2).

    rewrite mul_eq.
    elim (Nat.eq_dec n n0); intro.
    * rewrite a. rewrite Nat.compare_refl.
      rewrite mul_eq with (p:= Poly q1 n0 q2).
      rewrite Nat.compare_refl.


    rewrite mul_eq in IHp1.
    rewrite mul_eq in IHp1.
    destruct p2.
    rewrite mul_eq.
    rewrite mul_eq.
    
    rewrite IHq1.
    rewrite IHq2.
    rewrite Z.mul_comm.
    rewrite Z.mul_comm with (n:= z1).
    reflexivity. *)
    

Lemma mul_poly_val_comm (p q : valid_pol) (val:nat->Z) : 
(poly_val (mul_poly p q) val)%Z  = (poly_val (mul_poly q p) val)%Z.
Proof.
  destruct p as ( p & ? ).
  destruct q as ( q & ? ).
  unfold poly_val.
  unfold mul_poly.
  simpl.
  induction p.
  - unfold poly_val. simpl. induction q. simpl. 
    + rewrite Z.mul_comm. reflexivity.
    + apply valid_b_more in VP_prop1.
      destruct VP_prop1 as (validq1 & validq2).
      specialize (IHq1 validq1).
      specialize (IHq2 validq2).
      rewrite mul_eq.
      rewrite mul_eq with (p:=(Poly q1 n q2) ).
      reflexivity.
    
  - apply valid_b_more in VP_prop0.
    destruct VP_prop0 as (validp1 & validp2).
    specialize (IHp1 validp1).
    specialize (IHp2 validp2).
    simpl.
    
    induction q.
    + rewrite mul_eq.
    rewrite mul_eq with (p:=Cst z) (q:=(Poly p2 n p3)). reflexivity.
    +  
      apply valid_b_more in VP_prop1.
      destruct VP_prop1 as (validq1 & validq2).
      specialize (IHq1 validq1).
      specialize (IHq2 validq2).
      rewrite mul_eq.
      (* rewrite mul_eq with (p:=(Poly q1 n0 q2)). *)
      
      elim (Nat.eq_dec n n0); intro.
      * rewrite <- a. rewrite Nat.compare_refl. 
        (* simpl poly_val_.
        rewrite mul_eq with (p:=(Poly q1 n q2)).
        rewrite Nat.compare_refl.
        simpl poly_val_. *)

        rewrite <- a in IHp1.
        rewrite <- a in IHp2.

        (* rewrite mul_eq in IHp1.
        rewrite mul_eq with (p:=(Poly q1 n q2)) in IHp1. *)

        (* rewrite mul_eq.
        rewrite Z.mul_add_distr_l.
        rewrite Z.mul_add_distr_l.
        
        rewrite Z.add_assoc. *)

        destruct p2,p3.
        rewrite mul_eq in IHp1.
        (* rewrite mul_eq with (q:= Cst z) in IHp1. *)
        rewrite mul_eq in IHp2.
        (* rewrite mul_eq with (q:= Cst z0) in IHp2. *)
        
        -- rewrite mul_eq in IHp1. 
          simpl poly_val_ at 1 in IHp1.
          rewrite Z.mul_add_distr_l.
          rewrite Z.mul_add_distr_l.
          rewrite Z.add_assoc.
          rewrite IHp1.

          
          destruct p3.
          ++ rewrite mul_eq in IHp2. 
          simpl poly_val_ at 1 in IHp2.
          rewrite Z.add_assoc.

          
          rewrite Z.mul_add_distr_l.
          rewrite Z.add_assoc.
            rewrite IHp2.

        rewrite Z.add_comm.

        rewrite mul_eq in IHp1.
        rewrite mul_eq with (q:=p2) in IHp1.
         
        

      rewrite <- IHp2.
      rewrite <- IHp1.
      
  
      rewrite Z.mul_add_distr_r.
      rewrite <- Z.mul_assoc.

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
      destruct VP_prop1 as (validq1 & validq2).
      specialize (IHq1 validq1).
      specialize (IHq2 validq2).
      rewrite mul_eq. simpl. 
      rewrite IHq1.
      rewrite IHq2.
      intuition.
  - apply valid_b_more in VP_prop0.
    destruct VP_prop0 as (validp1 & validp2).
    specialize (IHp1 validp1).
    specialize (IHp2 validp2).
    simpl.
    rewrite mul_eq.
    induction q.
    + 
      rewrite Z.mul_add_distr_r.
      rewrite <- Z.mul_assoc.
      
      
      rewrite <- IHp2.
      rewrite <- IHp1.
      
      
      simpl.
      rewrite Z.mul_comm with (n:= ).
      rewrite Z.mul_comm.
      rewrite IHp2.
      reflexivity.
    rewrite IHp2.
    + 
    

    
    
    
    intuition.
      rewrite mul_eq in IHq1,IHq2. destruct q1, q2. simpl in *. 
      
      rewrite IHq1.
      
  - simpl. unfold poly_val. unfold mul_poly. simpl. rewrite mul_pol_0. reflexivity.
  - simpl. unfold poly_val.  unfold mul_poly. simpl. destruct (val n); unfold cst_poly; simpl VP_value; [rewrite mul_pol_1|rewrite mul_pol_0]; intuition. 
  - 
  -
  - 

Lemma to_poly_dec (f:form) (val:nat-> bool) : Z.eq (poly_val (to_poly f val) (fun x : nat => if val x then 1%Z else 0%Z)) 1%Z \/ Z.eq (poly_val (to_poly f val) (fun x : nat => if val x then 1%Z else 0%Z)) 0%Z.
Proof.
  induction f.
  - simpl. unfold poly_val. simpl. intuition.
  - simpl. unfold poly_val. simpl. intuition.
  - simpl. unfold poly_val. destruct (val n);  simpl; intuition.
  - simpl. 

    induction f1; unfold poly_val; simpl.
    + rewrite mul_pol_1. assumption.
    + rewrite mul_pol_0. assumption.
    + destruct (val n); simpl; [rewrite mul_pol_1|rewrite mul_pol_0]; intuition.
    + destruct IHf1.
    destruct (to_poly f1 val). simpl.  destruct (to_poly f2 val). simpl. 
    unfold poly_val in IHf1,IHf2. unfold VP_value in IHf1,IHf2. 
    induction VP_value0, VP_value1; destruct IHf1,IHf2. 
      * simpl in *.
        rewrite H.
        rewrite H0.
        rewrite Z.mul_1_l.
        unfold Z.eq. 
        left.
        reflexivity.
      * right.
        rewrite H.  
        rewrite mul_pol_1. 
        assumption.
      *  rewrite H.
        right. 
        rewrite mul_pol_0. 
        intuition.
      * rewrite H. rewrite H0.
        right.
        simpl.
        intuition.
      * rewrite H. 
        rewrite mul_pol_1.
        intuition.
      * rewrite H.
        rewrite mul_pol_1.
        intuition.
      * rewrite H.
        rewrite mul_pol_0.
        intuition.
      * rewrite H.
        rewrite mul_pol_0.
        intuition.
      * rewrite H0.
        (* unfold poly_val_ in H,H0. fold poly_val_ in H,H0. *)
        rewrite mul_pol_1_r. left. assumption.
      * rewrite H0.
        rewrite mul_pol_0_r. right. reflexivity.
      * rewrite H0.
        rewrite mul_pol_1_r. right. assumption.
      * rewrite H0.
        rewrite mul_pol_0_r. right. reflexivity.
      * rewrite mul_eq.
        
       (*  unfold poly_val_ in H0.   fold poly_val_ in H0. unfold poly_val_ in H. fold poly_val_ in H. *)

        elim (Nat.eq_dec n n0); intro.
        -- rewrite <- a. rewrite Nat.compare_refl. 
          unfold poly_val_ in H,H0.   fold poly_val_ in H,H0.
          unfold poly_val_. fold poly_val_.
          
          rewrite <- a in H0.
          destruct (val n).
          rewrite Z.mul_1_l. rewrite Z.mul_1_l.
          rewrite Z.mul_1_l in H. rewrite Z.mul_1_l in H0.
          unfold poly_val_. unfold poly_val_. fold poly_val_.
          ++ admit.
          ++ admit.
Abort.


Goal forall (f1 f2 : form) (val : nat -> bool),  (poly_val (to_poly f1 val) (fun x : nat => if val x then 1 else 0) =? 1)%Z &&
(poly_val (to_poly f2 val) (fun x : nat => if val x then 1 else 0) =? 1)%Z =
(poly_val (mul_poly (to_poly f1 val) (to_poly f2 val))
   (fun x : nat => if val x then 1 else 0) =? 1)%Z.
intros.
  induction f1; simpl.
  - unfold poly_val. unfold mul_poly. simpl. rewrite mul_pol_1. reflexivity.
  - unfold poly_val. unfold mul_poly. simpl. rewrite mul_pol_0. reflexivity.
  - destruct (val n).
    + unfold poly_val. unfold mul_poly. simpl. rewrite mul_pol_1. reflexivity.
    + unfold poly_val. unfold mul_poly. simpl. rewrite mul_pol_0. reflexivity.
  - 

(* Eval compute in (poly_val (to_poly (⊤ ∨ ⊥)) (fun x => 0%Z)). *)

Goal forall (f:form), forall (val:nat -> bool),  eval_form f val = Z.eqb (poly_val (to_poly f val) (fun x => if val x then 1%Z else 0%Z)) 1.
intro.

intro.
induction f.  
- intuition.
- intuition.
- simpl. destruct val; intuition.
- simpl.

  rewrite (IHf1 ).
  rewrite (IHf2 ).
  (* unfold poly_val. simpl. rewrite mul_eq.
  destruct ( (to_poly f1 val)).
  simpl.
  destruct (to_poly f2 val).
  simpl.
  destruct VP_value0.
  + destruct VP_value1.

  rewrite mul_eq.
  

  induction f1;  simpl.
  + unfold poly_val. simpl. 
    rewrite mul_pol_1.   reflexivity.

  + unfold poly_val. simpl. rewrite mul_pol_0. intuition. 
  + unfold poly_val. simpl.  destruct (val n); simpl.
    * rewrite mul_pol_1.  reflexivity.
    * rewrite mul_pol_0. intuition.

  +  *)

    
  induction f1.
  + simpl in *.
    unfold poly_val.
    unfold mul_poly.
    simpl.  
    rewrite mul_pol_1.
    reflexivity.
  + simpl in *.
    unfold poly_val.
    unfold mul_poly.
    simpl.  
    rewrite mul_pol_0.
    reflexivity.
  + simpl in *.
    unfold poly_val.
    unfold mul_poly.
    simpl.  
    destruct (val n).
    * simpl. rewrite mul_pol_1. reflexivity.
    * simpl. rewrite mul_pol_0. reflexivity.
  + simpl in *.
    unfold poly_val.
    unfold mul_poly.
    simpl.  

- admit.
- simpl.
  rewrite (IHf val).
  
Abort.


End BTauto.
 