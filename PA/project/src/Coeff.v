Require Import Maps BoolHelp PolyArith Valid.
Require Import PolyDefs.

Import ZArith NatMap F P.

Definition empty : monoid := NatMap.empty nat.


Theorem poly_equivalence (p:poly) : valid_b p = true <-> valid_pol p.
Proof.
  unfold iff. split; intro.
  - induction p.
    + constructor.
    + destruct p1,p2; simpl in H; andb_destr H; constructor.
      * intro. rewrite H0 in H. inversion H. 
      * auto.
      * destruct z; andb_destr H; auto.
      * destruct z; andb_destr H; intuition.
      * intro. rewrite H0 in H. inversion H.
      * destruct z; andb_destr H; intuition.
      * split; auto.
      * split; auto.
  - induction p; inversion H.
    + auto.
    + destruct y; auto. 
    + rewrite <- H0 in *. rewrite <- H2 in *. 
      specialize (IHp1 H5). 
      simpl in *.
      destruct x; andb_split; auto.
    + rewrite <- H0 in *. rewrite <- H3 in *.
      specialize (IHp2 H4).
      destruct x; andb_split; auto.
    + rewrite <- H0 in *. rewrite <- H3 in *.
      destruct H2. destruct H4.
      specialize (IHp1 H4).
      specialize (IHp2 H6).
      simpl; andb_split; auto.
Qed. 

Theorem leibniz : forall (p q : valid_poly), VP_value p = VP_value q -> p=q.
Proof.
  intros.
  destruct p, q.  
  simpl in H.
  subst.
  apply f_equal.
  apply BoolHelp.bool_irrel.
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
    destruct q; [destruct z|]; try (andb_destr H; rewrite Nat.ltb_irrefl in H); inversion H.
    
  + valid_destr H.
    specialize (IHp1 V0 m H0). 
    specialize (IHp2 V3).
    destruct (NatMap.find n m); [|apply IHp1].
    destruct n0; [apply IHp1|].
    simpl; rewrite Nat.sub_0_r.
    rewrite (IHp2 (add n n0 m)); [intuition|].
    destruct H0.
    exists x.
    rewrite F.add_neq_o; assumption.
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

Lemma neq_same {A} : forall (x:A), x <> x -> False .
Proof.
  intros. apply (H eq_refl).
Qed.

(* For any non-constant polynom [Poly p i q], there is a monoid with positive [i], for which the polynom coefficient is not 0 *)
Lemma coeffNot0 (p q : poly) (i : nat):
   valid_b (Poly p i q) = true -> 
   exists (m : monoid), get_coefficient_ (Poly p i q) m <> 0%Z /\
   exists (n:nat), NatMap.find i m = Some (S n).
Proof.
  revert p i.
  induction q; intros p i V.
  - valid_destr V.
    elim (Z.eq_dec z 0); intro.
    + rewrite a in *.
      apply valid_not0 in V. apply neq_same in V. contradiction.
    + exists (add i 1 empty).
      split.
      * erewrite coeff_remove_l with (n:=0); [| assumption| rewrite F.add_eq_o; intuition].
        erewrite <- get_coeff_add_add; [|assumption].
        simpl.
        intuition.
      * exists 0. rewrite F.add_eq_o; intuition.
  - valid_destr V.  
      destruct IHq2 with (p := q1) (i := n). assumption.
      destruct H. destruct H0.
      
      specialize (IHq2 p i V4) as Hp1.
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

Lemma all_coeff_distr (p1 p2 q1 q2 : poly) (i : nat) : 
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

Theorem all_coeff_eq (p q : valid_poly) : (forall (m : monoid), get_coefficient p m = get_coefficient q m) -> p = q.
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
  - induction q. 
    + intros. specialize (H empty). simpl in H. f_equal. assumption.
    + intros. 
      valid_destr propQ.
      apply coeffNot0 in propQ.
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
    eapply coeffNot0 in propP.
    destruct propP.
    specialize (H x).
    destruct H0.
    rewrite H in H0.
    simpl in H0.
    destruct H1.
    rewrite for_all_exist_pos in H0; [|  exists n; exists (S x0); rewrite H1; intuition].
    apply neq_same in H0. contradiction.
    + intros.
      valid_destr propQ. valid_destr propP. 
      elim (Nat.eq_dec n0 n); intro.
      * rewrite a in *. apply f_equal3 with (f:=Poly); [|intuition|].
        -- apply (IHp1 q1); [|assumption|assumption].
          apply all_coeff_distr with (p2:=p2) (i:=n) (q2:=q2) ; assumption.
        -- apply (IHp2 q2); [|assumption|assumption].
        apply all_coeff_distr with (p1:=p1) (p2:=p2) (i:=n) (q1:=q1) (q2:=q2); assumption .
      * apply coeffNot0 in propP as VP. destruct VP as (mP & ?).
        apply coeffNot0 in propQ as VQ. destruct VQ as  (mQ & ?).
        specialize (H mP) as HmP.
        specialize (H mQ) as HmQ.
        destruct H0, H1, H2, H3.
        elim (gt_eq_gt_dec n n0); intro.
        -- elim a; intro.
          ++ apply le_valid with (i:=n0) (p:=q1) (q:=q2) in propP; [|assumption|assumption].
            erewrite coeff_n_pos with (p:=(Poly q1 n0 q2)) (i:=n) (q:=p2) in HmP; [|assumption|exists x; intuition ].
            rewrite HmP in H0.
            apply neq_same in H0. contradiction.
          ++ rewrite b0 in b. apply neq_same in b. contradiction.
        -- apply le_valid with (i:=n) (p:=p1) (q:=p2) (q':=q2) in propQ; [|assumption|assumption].
          rewrite coeff_n_pos with (p:=(Poly p1 n p2)) (i:=n0) (q:=q2) in HmQ; [ |assumption | exists x0; assumption ].
          rewrite <- HmQ in H1.
          specialize (H1 eq_refl); contradiction.
Qed.

