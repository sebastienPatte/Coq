Require definitions.
Check definitions.monoid.
Import definitions.
Import F P NatMap FMapList.
Definition empty : monoid := NatMap.empty nat.


Check empty.
Check monoid.

Require Import valid.

Require Import ZArith Arith Bool Lia.

Require Import bool_help.

Hint Resolve leb_complete : core. 
Hint Resolve leb_correct : core. 
Hint Resolve ltb_correct : core. 
Hint Resolve ltb_complete : core.
Hint Resolve Nat.ltb_lt : core.
Hint Resolve Nat.sub_0_r Nat.lt_le_incl ltb_imp_leb ltb_trans leb_trans ltb_leb_trans: core.

Require Import maps.

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
(Poly p1 i q1) = (Poly p2 i q2).
Proof.
  intro.
  destruct H.
  rewrite H.
  rewrite H0.
  reflexivity.
Qed.


Theorem poly_equivalence (p:poly) : valid_b p = true <-> valid_poly p.
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

Definition p1 := (Poly (Cst 0) 2 (Cst 1)).





Theorem leibniz : forall (p q : valid_pol), VP_value p = VP_value q -> p=q.
Proof.
  intros.
  destruct p.
  destruct q.  
  simpl in H.
  subst.
  apply f_equal.
  apply bool_irrel.
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

Theorem all_coeff_eq (p q : valid_pol) : (forall (m : monoid), get_coefficient p m = get_coefficient q m) -> p = q.
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
          apply all_coeff_dec with (p2:=p3) (i:=n) (q2:=q2) ; assumption.
        -- apply (IHp2 q2); [|assumption|assumption].
        apply all_coeff_dec with (p1:=p2) (p2:=p3) (i:=n) (q1:=q1) (q2:=q2); assumption .
      * apply coeffNot0 in propP as VP. destruct VP as (mP & ?).
        apply coeffNot0 in propQ as VQ. destruct VQ as  (mQ & ?).
        specialize (H mP) as HmP.
        specialize (H mQ) as HmQ.
        destruct H0, H1, H2, H3.
        elim (gt_eq_gt_dec n n0); intro.
        -- elim a; intro.
          ++ apply le_valid with (i:=n0) (p:=q1) (q:=q2) in propP; [|assumption|assumption].
            erewrite coeff_n_pos with (p:=(Poly q1 n0 q2)) (i:=n) (q:=p3) in HmP; [|assumption|exists x; intuition ].
            rewrite HmP in H0.
            apply neq_same in H0. contradiction.
          ++ rewrite b0 in b. apply neq_same in b. contradiction.
        -- apply le_valid with (i:=n) (p:=p2) (q:=p3) (q':=q2) in propQ; [|assumption|assumption].
          rewrite coeff_n_pos with (p:=(Poly p2 n p3)) (i:=n0) (q:=q2) in HmQ; [ |assumption | exists x0; assumption ].
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

Lemma val_is_cst (p:poly) (z:Z): valid_b p = true -> (forall (f: nat -> Z), poly_val_ p f = z ) -> 
(forall (m: monoid ), get_coefficient_ p m = get_coefficient_ (Cst z) m).
Proof.
  intro.
  revert z.
  induction p.
  - intros.
    elim (Z.eq_dec z0 z); intro.
    + rewrite a in *.  reflexivity.
    + exfalso. apply b. 
      specialize (H0 (fun x => 0%Z)). simpl in H0.
      auto.
  - intros.
    elim (Z.eq_dec z 0); intro.
    + rewrite a in *.
      eapply coeffNot0 in H as H1.
      destruct H1.
      destruct H1.
      (* eapply coeff_n_pos with (p:=p2) (q:=p3) in H2 as H3. *)
      destruct H2.
      erewrite coeff_remove_l with (n:=x0) in H1; try assumption.
      valid_destr H.
      specialize (IHp1 V0). specialize (IHp2 V1).
      simpl in H0.
      
    

    admit.
    

Abort.


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
  end
.  

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
    end 
  in
  aux a l O 
.

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
Abort.

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


Definition is_null (p:poly) : bool := 
  match p with 
  |Cst 0 => true 
  |_=> false 
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
          eapply le_weak_valid with (p:=q1) (q:=q2) (p':=p2) (q':=p3) in a0 as a2; try assumption.
          specialize (IHp1 (Poly q1 n0 q2) VQ) as HN1.
          eapply weak_sum_gt' with (p2:=p3) (q2:=p3) (p:=p2); assumption.
        -- rewrite b in *. rewrite Nat.compare_refl.
          specialize (IHp1 q1 V2) as HN1.
          specialize (IHp2 q2 V3) as HN2.
          eapply weak_sum_gt' with (p2:=p3) (q2:=q2) (p:=p2); try assumption.
          eapply weak_sum_leq' with (p1:=p2) (q1:=q1) (q:=p3); try assumption. 
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
    elim (b_dec (is_null (remove_null_r p3)) true); intro.
    + rewrite H1.
      simpl in H0. 
      rewrite H1 in H0.
      destruct (remove_null_r p2).
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
      destruct p2.
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
    elim (b_dec (is_null (remove_null_r p3)) true); intro.
    + specialize (IHp1 V0). simpl remove_null_r. rewrite H0. assumption. 
    + rewrite not_true_iff_false in H0.
      simpl.
      intuition.
      rewrite H0.
      eapply not_null_leq with (i:=n) (p:=p2) in H0.

      destruct (remove_null_r p3).
      * destruct z. inversion H0. 
        -- elim (b_dec (is_null (remove_null_r p2)) true); intro.
          ++ rewrite is_null_is_0 in H3. rewrite H3.
            simpl remove_null_r.
            simpl. 
            reflexivity.
          ++ rewrite not_true_iff_false in H3.
            intuition.
            eapply not_null_le with (i:=n) (q:=p3) in H3.
            destruct (remove_null_r p2).
            destruct z. inversion H1.
            reflexivity. 
            reflexivity.
            reflexivity.
            eapply le_valid with (p':=Cst 0). 
            intuition.
            assumption.
            simpl. reflexivity.
            assumption.
        --  elim (b_dec (is_null (remove_null_r p2)) true); intro.
        ++ rewrite is_null_is_0 in H3. rewrite H3.
          simpl remove_null_r.
          simpl. 
          reflexivity.
        ++ rewrite not_true_iff_false in H3.
          intuition.
          eapply not_null_le with (i:=n) (q:=p3) in H3.
          destruct (remove_null_r p2).
          destruct z. inversion H3.
          reflexivity. 
          reflexivity.
          eapply le_valid with (p':=Cst 0). 
          intuition.
          assumption.
          simpl. reflexivity.
          assumption.
        * elim (b_dec (is_null (remove_null_r p2)) true); intro.
          -- rewrite is_null_is_0 in H3. rewrite H3.
            eapply leq_valid with (q:=Cst 1).
            auto.
            simpl. reflexivity.
            intuition.
          -- rewrite not_true_iff_false in H3.
            intuition.
            eapply not_null_le with (i:=n) (q:=p3) in H3.
            destruct (remove_null_r p2).
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
    + eapply weak_mul_gt' with (p:=p2) (p2:=p3) (q2:=p3); try assumption.
      * simpl. destruct p3. reflexivity. andb_split. apply weak_valid_leq in H. auto. assumption.
      * eapply weak_mul_leq' with (q1:=p2) (q:=p3) (p1:=p2); try assumption.
      destruct p2; simpl. reflexivity. andb_split. apply weak_valid_le in H. auto. assumption.
    
    + rewrite Nat.compare_refl.
      weak_valid_destr H. weak_valid_destr H0.
      elim (gt_eq_gt_dec n0 n); intro.
      * elim a; intro.
        -- apply nat_compare_gt in a0 as a1.
          rewrite a1.
            
          apply weak_val_mul_gt with (n:=n) (n0:=n0) (p2:=p2) (p3:=p3) (q1:=q1) (q2:=q2) in IHp1; try assumption.
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
        
        eapply weak_val_mul_eq with (p2:=p2) (n:=n) (p3:=p3) in IHp1; auto.
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

      eapply weak_mul_gt' with (p:=p2) (p2:=p3) (q2:=p3); try assumption.
      eapply le_weak_valid with (p':=p2); try assumption.
      
      eapply weak_mul_leq' with (p1:=p2) (q1:=p2) (q:=p3); try assumption.

      eapply leq_weak_valid with (q:=p3); auto.
      
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
    (* rewrite mul_pol_1.
    rewrite mul_pol_1.
    reflexivity.
Qed. *)
Admitted.

Lemma mul_pol_0_r : forall (p:poly) (val:nat -> Z), Z.eq (poly_val_ (mul_poly_ p (Cst 0)) val)  0%Z .
Proof.
  intros.
  induction  p.
  - simp mul_poly_.  rewrite Z.mul_0_r. reflexivity.
  - simp mul_poly_. 
    simpl.
    (* rewrite mul_pol_0.
    rewrite mul_pol_0.
    simpl.
    rewrite Z.mul_0_r.
    reflexivity.
Qed. *)

Admitted.

Hint Rewrite Z.mul_0_r : core.

Require Import Lia.

Definition z_of_bool := (fun x : bool => if x then 1%Z else 0%Z).


Lemma valid_remove_null (p:poly) : 
valid_b p = true ->
remove_null_r p = p.
Proof.
  intro.
  induction p.
  - simpl. reflexivity.
  - simpl.
    valid_destr H.
    elim (b_dec (is_null (remove_null_r p3)) true); intro.
    + apply is_null_is_0 in H0 as H1. rewrite (IHp2 V1) in H1.
      rewrite H1 in H.
      destruct p2; inversion H.
    + rewrite not_true_iff_false in H0.
      rewrite H0.
      
       rewrite (IHp1 V0).
       rewrite (IHp2 V1).
       reflexivity.
Qed.


Lemma sum_poly_val (p q : valid_pol) (val:nat->Z) : 
(poly_val (sum_poly p q) val)  = ( (poly_val p val) + (poly_val q val))%Z.
Proof.
  destruct p as ( p & ? ).
  destruct q as ( q & ? ).
  unfold poly_val.
  unfold sum_poly.
  simpl.
  induction p.
  -  simpl. induction q;  simp sum_poly_; simpl. 
    +  reflexivity.
    + valid_destr VP_prop0.
      specialize (IHq1 V0). specialize (IHq2 V1).
      elim (b_dec (is_null (remove_null_r q2)) true); intro.
      * rewrite is_null_is_0 in H. 
        rewrite valid_remove_null in H; [|assumption].
        rewrite H in VP_prop0.
        destruct q1; inversion VP_prop0.
      * rewrite not_true_iff_false in H.
        rewrite H.
        simpl.
        rewrite IHq1.
        rewrite valid_remove_null; [|assumption].
        lia.
  - valid_destr VP_prop. specialize (IHp1 V0).  specialize (IHp2 V1).
    simpl.
    induction q; simp sum_poly_; simpl.
    + elim (b_dec (is_null (remove_null_r p3)) true); intro.
      * rewrite is_null_is_0 in H. 
        rewrite valid_remove_null in H; [|assumption].
        rewrite H in VP_prop.
        destruct p2; inversion VP_prop.
      * rewrite not_true_iff_false in H.
        rewrite H.
        simpl.
        rewrite IHp1.
        rewrite valid_remove_null; [|assumption].
        simpl.
        lia.
    + destruct (n ?= n0).
      * 


Abort.

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
    + valid_destr VP_prop0.
      specialize (IHq1 V0). specialize (IHq2 V1).
      simp mul_poly_.
      simpl .

Abort.

  

