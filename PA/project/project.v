Require Import ZArith Bool.

Inductive poly : Type :=
| Cst : Z -> poly
| Poly : poly -> nat -> poly -> poly .

(* 
  Fixpoint valid_b (p:poly) (i:nat) : bool := 
  match p with 
  |Cst _ => true
  |Poly p j (Cst 0) => false
  |Poly p j q => 
  	Nat.leb i j && 
  	valid_b p (S j) && valid_b q j 
  end. 

  Definition valid_bool (p:poly) : valid_b p 0. 
*)

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

Lemma valid_b_more (p q : poly) (i:nat) : 
  valid_b (Poly p i q) = true -> valid_b p = true /\ valid_b q = true.
Proof.
  intro.
  split.
  induction p; simpl in H; intuition.
  - destruct q.
  elim (Z.eq_dec z 0); intro; destruct z; intuition; rewrite andb_true_iff in H;
  destruct H; intuition.
  
  do 2 (rewrite andb_true_iff in H; destruct H).
  simpl.
  assumption.
  - destruct p,q; simpl in H; intuition.
    + rewrite andb_true_iff in H.
      destruct H.
      simpl.
      assumption.
    + do 2 (rewrite andb_true_iff in H; destruct H).
      simpl. 
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

    (* rewrite <- H3 in IHp2.
    apply IHp2 in H5. *)

    rewrite <- H0 in IHp1.
    apply IHp1 in H4.
      simpl.
      simpl in H4.
      
      
      repeat (rewrite andb_true_iff;split;try (apply leb_correct); intuition).
      
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

Require Import FMapList.
Require Import Coq.FSets.FMapList.
Require Import Coq.Structures.OrderedTypeEx.
Module Import NatMap := FMapList.Make(Nat_as_OT).


Definition monoid : Type := NatMap.t nat.

(* We could make a single definition [get_coefficient] with a dependent match to keep the polynomials proofs of validity at each recursive call, but it makes the proofs harder. Instead we use the following definitions, with the lemma [valid_b_more] to propagate the polynomials validity proofs at each recursive call *)

Fixpoint get_coefficient_ (pol: poly) (m:monoid) := 
  match pol with 
  | Cst z => if (fold (fun k v (acc:bool) => acc && (v=?0)) m true) then z else 0%Z 
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

Eval compute in (get_coefficient_ poly1 mymap).
Eval compute in (get_coefficient_ poly2 mymap2).
Eval compute in (get_coefficient_ poly1 (NatMap.empty nat)).
Eval compute in (get_coefficient_ poly2 (NatMap.empty nat)).

Definition empty_mono : monoid := NatMap.empty nat.

(* X0 X0 *)
Definition mymap3 := NatMap.add 0 2 (NatMap.empty nat).
Eval compute in (get_coefficient_ poly1 mymap3).

Require Import
  Coq.FSets.FMapFacts.

  Module P := WProperties_fun Nat_as_OT NatMap.
  Module F := P.F.

(* Lemma posCoeff (p q : poly) (i:nat) : 
  valid_b (Poly p i q) = true -> 
  exists (m : monoid), (get_coefficient_ (Poly p i q) m) <> 0%Z .
Proof.
  intro.
  induction q.
  unfold get_coefficient_.
  - elim (Z.eq_dec z 0%Z ); intro.
    + simpl in H.
      destruct p.
      rewrite a in H.
      intuition.
      rewrite a in H.
      intuition.
    + 
      fold get_coefficient_.
      elim (Z.eq_dec (get_coefficient_ p (add i 1 empty_mono)) 0); intro.
      exists (add i 1 empty_mono).
      rewrite a.
      simpl.
      erewrite F.add_eq_o; [|reflexivity].
      simpl.
      erewrite P.fold_Equal with (m2:= add i 0 empty_mono).
      erewrite P.fold_add with (k:=i) (e:=0).
      erewrite P.fold_Empty.
      simpl.
      assumption.



      intuition.
      apply empty_1.
      intuition.
      intuition.
      unfold P.transpose_neqkey; intuition.
      admit.
      intro.
      admit.
      intuition.
      intuition.
      unfold P.transpose_neqkey; intuition.
      admit.
      unfold Equal.
      intro.
      elim (Nat.eq_dec i y); intro.
      rewrite a0.
      erewrite F.add_eq_o; [|reflexivity].
      erewrite F.add_eq_o; [|reflexivity].
      reflexivity.

      erewrite F.add_neq_o; [|assumption].
      erewrite F.add_neq_o; [|assumption].
      erewrite F.add_neq_o; [|assumption].
      reflexivity.

      induction p.
      exists (empty_mono).
      simpl.
      intuition.

      exists (add i 1 empty_mono).
      erewrite F.add_eq_o; [|reflexivity].
      
      
      erewrite P.fold_Equal with (m2:= add i 0 empty_mono).
      erewrite P.fold_add with (k:=i) (e:=0).
      erewrite P.fold_Empty.
      simpl. with (k:=i) (e:=0).
      intuition.
      intuition.
      intuition.
      intuition.
      unfold P.transpose_neqkey; intuition.
      admit.
      intro.
      admit.
      intuition.
      intuition.
      unfold P.transpose_neqkey; intuition.
      admit.
      unfold get_coefficient_.

      unfold NatMap.In.
      
      fold get_coefficient_.
      
      

Admitted. *)
  
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
  -
    simpl in H.
    
    apply valid_b_more in VP_prop1 as validV.
    destruct validV as (validV1 & validV2).
    specialize (IHVP_value1_1 validV1).
    specialize (IHVP_value1_2 validV2).
    destruct VP_value1_1. 
    
    + elim (Z.eq_dec z z0); intro.
      * rewrite <- a in IHVP_value1_1. 
        unfold VP_value in IHVP_value1_1.
        unfold VP_value in IHVP_value1_2.

        (* specialize (H (empty_mono)) as Hempty.
        erewrite P.fold_Empty in Hempty; [ | intuition |apply empty_1  ].
        erewrite F.empty_o in Hempty.

        specialize (H (add n 1 empty_mono)) as Hn1.
        erewrite F.add_eq_o in Hn1; [|reflexivity].
        simpl in Hn1.
        
        specialize (H (add n 2 empty_mono)) as Hn2.
        erewrite F.add_eq_o in Hn2; [|reflexivity].
        simpl in Hn2. *)

        (* edestruct (fold (fun (_ : key) (v : nat) (acc : bool) => acc && (v =? 0)) m true) in H. *)

        induction VP_value1_2.
        
      -- specialize (H (add n 1 empty_mono)).
        simpl in H.
        erewrite F.add_eq_o in H; intuition; simpl in H.
        erewrite P.fold_Equal with (m2:= add n 0 (empty nat)) in H. 
        erewrite P.fold_add with (k:=n ) (e:=0) in H; intuition; simpl in H.
        ++ admit. (* z1 can't be 0%Z *) 
        ++ unfold P.transpose_neqkey.
        intuition. admit. (* reorder boolean equalities *)
        ++ admit. (* z1 can't be 0%Z *) 
        ++ intuition.
        ++ intuition.
        ++ unfold P.transpose_neqkey.
        intuition. admit. (* reorder boolean equalities *)
        ++ unfold Equal.
        intuition.
        elim (Nat.eq_dec y n); intro.
        erewrite F.add_eq_o ; intuition.
        erewrite F.add_eq_o ; intuition.
        erewrite F.add_neq_o ; intuition.
        erewrite F.add_neq_o ; intuition.
        erewrite F.add_neq_o ; intuition.
      -- assert (validV21 : valid_b (Poly (Cst z0) n VP_value1_2_1) =true).
        admit. 
      specialize (IHVP_value1_2_1 validV21).
      assert (validV22 : valid_b (Poly (Cst z0) n VP_value1_2_2) =true).
        admit. 
      specialize (IHVP_value1_2_2 validV22).
      
      
      admit.
    * 

    specialize (H (empty_mono)) as Hempty.
    erewrite P.fold_Empty in Hempty; [ | intuition |apply empty_1  ].
    erewrite F.empty_o in Hempty.
    intuition.
  + 

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
      reflexivity.
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
| f_imp 	: form -> form -> form
.
Fixpoint eval_form (f:form) (val : nat -> bool) : bool := 
  match f with 
  | f_true => true
  | f_false => false
  | f_var i => val i
  | f_and f1 f2 => eval_form f1 val && eval_form f2 val
  | f_or f1 f2 => eval_form f1 val || eval_form f2 val
  | f_not f1 => negb (eval_form f1 val	)
  | f_imp f1 f2 => impb (eval_form f1 val) (eval_form f2 val)
  end.  


Hint Constructors form : core.
Notation "A ∧ B" := (f_and A B) (at level 30, right associativity).
Notation "A ∨ B" := (f_or A B) (at level 35, right associativity).
Notation "A → B" := (f_imp A B) (at level 49, right associativity, B at level 50).
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
|impb ?x ?y => 
  match read_term x l with
  |(?x' , ?l') => match read_term y l' with
    |(?y' , ?l'') => constr:(( f_imp x' y' , l''))
  end end
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

Program Fixpoint sum_poly (p q:poly) {measure (length p + length q) } := 
  match p,q with 
  |Cst z1, Cst z2 => Cst (Z.add z1 z2)
  |Poly p1 i q1, Cst z2 => 
    Poly (sum_poly p1 (Cst z2)) i q1
  |Cst z1, Poly p2 j q2 => 
  Poly (sum_poly p2 (Cst z1)) j q2
  |Poly p1 i q1, Poly p2 j q2 => 
    if i =? j 
    then Poly (sum_poly p1 p2) i (sum_poly q1 q2)
    else Poly (sum_poly p1 (Poly p2 j q2)) i q1
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

Eval compute in (sum_poly pol1 pol2).


Program Fixpoint mul_poly (p q:poly) {measure (length p + length q) } := 
  match p,q with 
  |Cst z1, Cst z2 => Cst (Z.mul z1 z2)
  |Poly p1 i q1, Cst z2 => 
    Poly (mul_poly p1 (Cst z2)) i (mul_poly q1 (Cst z2))
  |Cst z1, Poly p2 j q2 => 
  Poly (mul_poly p2 (Cst z1)) j (mul_poly q2 (Cst z1))
  |Poly p1 i q1, Poly p2 j q2 => 
    match Nat.compare i j with 
    |Lt => Poly (mul_poly p1 (Poly p2 j q2)) i (mul_poly q1 (Poly p2 j q2))
    |Gt => Poly (mul_poly p2 (Poly p1 i q1)) j (mul_poly q2 (Poly p1 i q1))
    |Eq => Poly (mul_poly p1 p2) i (Poly (mul_poly p1 q2) j (mul_poly q1 q2)) 
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

Eval compute in (mul_poly pol1 pol2).



(* 
Fixpoint mpplus n (c : Z) (m : monom n) (p : poly n) : poly n :=
  match p with
    | nil => (c,m) :: nil
    | cons (c',m') p' =>
      match monom_eq_dec m m' with
	| left _ => (c+c',m) :: p'
	| right _ => (c',m') :: mpplus c m p'
      end
  end.

Fixpoint pplus n (p1 p2 : poly n) : poly n :=
  match p1 with
    | nil => p2
    | cons (c,m) p' => mpplus c m (pplus p' p2)
  end.
  
Definition mmult n (m1 m2 : monom n) := Vmap2 plus m1 m2.

Definition mpmult n c (m : monom n) (p : poly n) :=
  map (fun cm => (c * fst cm, mmult m (snd cm))) p.

Fixpoint pmult n (p1 p2 : poly n) : poly n :=
  match p1 with
    | nil => nil
    | cons (c,m) p' => mpmult c m p2 + pmult p' p2
  end.
  
*)


Definition mul_poly (p q:valid_pol) := p.

Definition sub_poly (p q:valid_pol) := sum_poly p (mul_poly (cst_poly (-1)%Z) q).

Fixpoint to_poly (f:form) (val:nat->bool) := 
match f with 
|f_true => cst_poly 1%Z
|f_false => cst_poly 0%Z
|f_and a b => mul_poly (to_poly a val) (to_poly b val)
|f_or a b => sub_poly (sum_poly (to_poly a val) (to_poly b val)) (mul_poly (to_poly a val) (to_poly b val))
|f_not a =>  sub_poly (cst_poly 1%Z) (to_poly a val)
|f_var n => if (val n) then cst_poly 1%Z else cst_poly 0%Z 
|f_imp a b => sub_poly (sum_poly (sub_poly (cst_poly 1%Z) (to_poly a val)) (to_poly b val)) (mul_poly (sub_poly (cst_poly 1%Z) (to_poly a val)) (to_poly b val))
end.





(* Eval compute in (poly_val (to_poly (⊤ ∨ ⊥)) (fun x => 0%Z)). *)

Goal forall (f:form), forall (val:nat -> bool),  eval_form f val = Z.eqb (poly_val (to_poly f val) (fun x => if val x then 1%Z else 0%Z)) 1.
intro.

induction f; intro.  
- intuition.
- intuition.
- simpl. destruct val; intuition.
- simpl. 
Abort.


End BTauto.