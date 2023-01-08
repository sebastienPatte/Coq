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


      Search ( _ <=? _ = true -> _ <= _).


Definition p1 := (Poly (Cst 0) 2 (Cst 1)).




Require Import Coq.Program.Equality.
Require Import Coq.Logic.ProofIrrelevance.
Require Import Coq.Logic.Eqdep_dec.


Record valid_pol : Type :=
{ VP_value : poly ;
VP_prop : valid_b VP_value = true }.



Lemma leibniz : forall (p q : valid_pol), VP_value p = VP_value q -> p=q.
Proof.
  Print eq_sig.
  intros.
  
  destruct p.
  destruct q.
  
  simpl in H.
  
  subst.
  apply f_equal.
  apply proof_irrelevance. (* allowed ? can be deduced from dep eq elim ? *)
Qed.

Print eq_rect.
Print eq_rect_eq_dec.

(* https://cstheory.stackexchange.com/questions/5158/prove-proof-irrelevance-in-coq *)

Definition eq_elim_dep A t u (y:A) (e : @eq A t u) (e' : @eq A t y) (y:A) := 
  match e as e' in eq _ y with 
    eq_refl => t
  end.

  Check eq_elim_dep.


(* Inductive mono : Type :=
| Empty : mono
| Mono (i:nat) (n:nat) :  mono. *)
(* [i] is the indice of the variable X_i and [n] its power in the monomial *)

(* https://www.di.ens.fr/~quyen/publication/ly10.pdf *)

Require Import PArray.
Require Import Vector.

(* Inductive vector {A} : nat -> Type :=
| Vnil : vector 0
| Vcons : forall (a:A)(n:nat), vector n -> vector (S n). *)

Inductive mono : Type := 
  | Mnil : mono
  | Mcons : nat -> nat -> mono -> mono. 
  
  Require Import Bool.BoolEq.

Require Import NArith.
Check beq_nat.

Fixpoint mono_get (m:mono) (i:nat) : nat := 
  match m with 
  |Mnil => 0
  |Mcons j n m' => 
    if (beq_nat i j)
    then n + mono_get m' i
    else mono_get m' i
  end.

Definition mono1 := Mcons 0 1 (Mcons 1 1 Mnil).

Eval compute in (mono_get mono1 1).

Check List.nth_error.


Fixpoint get_coeff (pol: poly) (m:mono) := 
  match pol with 
  | Cst z => (match m with |Mnil => z |_ => 0%Z end)
  | Poly p i q => 
    match mono_get m i with 
      |0 => get_coeff p m
      |S n => Z.add (get_coeff p m) (get_coeff q m)
      end
end.

(* 3 X0 X1 + 2 X0 X0 + 1 *)
Definition poly1 := (Poly (Cst 1%Z) 0 (Poly (Poly (Cst 0%Z) 1 (Cst 3%Z)) 0 (Cst 2%Z))).

Eval compute in (get_coeff poly1 mono1).

Require Import FMapList.
Require Import Coq.FSets.FMapList.
Require Import Coq.Structures.OrderedTypeEx.
Module Import NatMap := FMapList.Make(Nat_as_OT).


Definition monoid : Type := NatMap.t nat.

Fixpoint get_coefficient_ (pol: poly) (m:monoid) := 
  match pol with 
  | Cst z => if (fold (fun k v (acc:bool) => acc && (v=?0)) m true) then z else 0%Z 
  | Poly p i q => 
    match find i m with 
      |None => get_coefficient_ p m
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

  induction VP_value0; induction VP_value1; simpl.

  - specialize (H empty_mono). simpl in H. f_equal. assumption.
  - unfold VP_value in IHVP_value1_1.
    unfold VP_value in IHVP_value1_2.
    simpl in H.
    destruct VP_value1_1. 
    
    
    assert (validV1 : valid_b (Cst z) = true); [intuition|].
        specialize (IHVP_value1_1 validV1).
        assert (validV2 : valid_b VP_value1_2 = true).
          unfold valid_b in VP_prop1.
          destruct VP_value1_2; intros.
          intuition.
          rewrite andb_true_iff in VP_prop1.
          intuition.
    specialize (IHVP_value1_2 validV2).
        

    + elim (Z.eq_dec z z0); intro.
      * rewrite <- a in IHVP_value1_1. 
        unfold VP_value in IHVP_value1_1.
        unfold VP_value in IHVP_value1_2.

        specialize (H (empty_mono)) as Hempty.
        erewrite P.fold_Empty in Hempty; [ | intuition |apply empty_1  ].
        erewrite F.empty_o in Hempty.

        specialize (H (add n 1 empty_mono)) as Hn1.
        erewrite F.add_eq_o in Hn1; [|reflexivity].
        simpl in Hn1.
        
        specialize (H (add n 2 empty_mono)) as Hn2.
        erewrite F.add_eq_o in Hn2; [|reflexivity].
        simpl in Hn2.
        
        
        

        


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
      simpl in H.      

      admit.
    * 

    specialize (H (empty_mono)) as Hempty.
    erewrite P.fold_Empty in Hempty; [ | intuition |apply empty_1  ].
    erewrite F.empty_o in Hempty.
    intuition.
  + 
  (* unfold VP_value in IHVP_value1_1.
  unfold VP_value in IHVP_value1_2.
        specialize (H (add n 1 empty_mono)) as mn1.
        simpl in mn1.
        erewrite F.add_eq_o in mn1.
        simpl in mn1.
        erewrite F.add_eq_o in mn1.
        simpl in mn1.
        erewrite P.fold_Equal with (m2:= add n 0 (empty_mono)) in mn1. 
        erewrite P.fold_add with (k:=n ) (e:=0) in H; intuition; simpl in H.
        specialize (H2 (add n 1 empty_mono)).
        admit.
        admit.
        admit.
        admit.
        admit.
        admit.
        admit.
        admit.
        
    + 
    specialize (H ( empty_mono)). 
    simpl in H.

    erewrite F.add_eq_o in H; intuition.
    erewrite P.find_add with (k:=n ) (e:=2) in H; intuition.
    destruct VP_value1_2.
  
    inversion VP_prop1.
    (* destruct VP_value1_1, VP_value1_2; simpl in IHVP_value1_1, IHVP_value1_2, H .
    + Check poly_equivalence.
      (* rewrite poly_equivalence in IHVP_value1_1.
      destruct z1. *)
      elim (Z.eq_dec z z0); intro.

      * rewrite a in IHVP_value1_1.
        simpl in IHVP_value1_1. 
        Search (_=_).
        rewrite eq_refl in IHVP_value1_1. apply eq_refl in IHVP_value1_1. f_equal. 
        apply VP_prop0  in IHVP_value1_1.
        replace (VP_value1_1) with (Cst z) in *. 
        replace (VP_value1_2) with (Cst z) in *.
     *)
     induction VP_value1_1, VP_value1_2; simpl in *.
     + 
       elim Z.eq_dec with (x:= z1) (y:= 0%Z).
       * intro.
       rewrite a in VP_prop1.
       intuition.
 
       * intro.
       (* elim Z.eq_dec with (x:= z) (y:= z1). *)
       -- 
       specialize (H (add n 1(NatMap.empty nat))). simpl in *.
         (* intro. *)
         rewrite find_1 with (e:=1) in H.
         simpl in H.
         Search (fold _ _ ).
         (* erewrite F.add_mapsto_iff in H. *)
 
         ++ erewrite P.fold_Equal with (m2:= add n 0 (empty nat)) in H. 
         (* erewrite F.add_in_iff in H; intuition. *)
         
           erewrite P.fold_add with (k:=n ) (e:=0) in H; intuition.
           intuition.
           intuition.
           unfold P.transpose_neqkey.
           intuition.
           rewrite <- andb_assoc.
           rewrite <- andb_assoc.
           rewrite andb_comm with (b1:= e' =? 0).
           reflexivity.
           unfold Equal.
           intro.
           Check Z.eq_dec.
           Search ( {_ = _} + {_ <> _}).
           eelim Nat.eq_dec with (n:=y) (m:= n).
           ** intro.
             erewrite F.add_eq_o; intuition.
             erewrite F.add_eq_o; intuition.
           ** intro.
           erewrite F.add_neq_o; intuition.
           erewrite F.add_neq_o; intuition.
           erewrite F.add_neq_o; intuition.
         ++ erewrite F.add_mapsto_iff.
           intuition.
    
    + rewrite andb_true_iff in H1.
      destruct H1. 
      specialize (IHVP_value1_2 H1).
      simpl in IHVP_value1_1.dv
      
      erewrite H in IHVP_value1_2.
     (***********************************************************************)
     specialize (IHVP_value1_2 ((NatMap.empty nat))). simpl in *.
       simpl in H.
       rewrite H.
       simpl in *.
       revert H1.
       eapply IHVP_value1_2.
         (* erewrite P.fold_add with (k:=n ) (e:=1) in H; intuition. *)
           erewrite P.fold_Empty in H; intuition.
           simpl in H.
 
      erewrite fold_1 in H.
 
       eapply elements_1 in H.
       
 
       elim Z.eq_dec with (x:= z1) (y:= z).
       intros.
       rewrite a.
       rewrite a0.
       specialize (H (NatMap.add n 2 (NatMap.empty nat))). simpl in *.
       rewrite a in H.
       unfold empty in H.
       re
       
       unfold elements in H.
       unfold Raw.elements in H.
       simpl in H.
       Check (Nat_as_OT.eq_refl).
 
       unfold Nat_as_OT.compare in H.
       
       rewrite nat_compare_eq in H.
       rewrite <- Nat.compare_refl in H.
       
       (* replace (n ?= n) with (Eq) in H; [|rewrite Nat.compare_refl with (x:=n); reflexivity]. *)
       
       simpl in H using Nat.compare_refl.
       
       rewrite <- Nat_as_OT.eq_dec in H.
     unfold empty in H. erewrite empty_1 in H.
   



(*  *)
  
  unfold get_coefficient.
  destruct p,q.
  simpl.
  intro.
  apply leibniz.
  induction VP_value0, VP_value1; simpl in *.
  - specialize (H empty_mono). simpl in H. f_equal. assumption.
  - (* specialize (H (NatMap.add n 1 (NatMap.empty nat))). simpl in *.
    rewrite find_1 with (e:=1) in H. simpl in *. *)
    induction VP_value1_1, VP_value1_2; simpl in *.
    + 
      elim Z.eq_dec with (x:= z1) (y:= 0%Z).
      * intro.
      rewrite a in VP_prop1.
      intuition.

      * intro.
      (* elim Z.eq_dec with (x:= z) (y:= z1). *)
      -- 
      specialize (H (add n 1(NatMap.empty nat))). simpl in *.
        (* intro. *)
        rewrite find_1 with (e:=1) in H.
        simpl in H.
        Search (fold _ _ ).
        (* erewrite F.add_mapsto_iff in H. *)

        ++ erewrite P.fold_Equal with (m2:= add n 0 (empty nat)) in H. 
        (* erewrite F.add_in_iff in H; intuition. *)
        
          erewrite P.fold_add with (k:=n ) (e:=0) in H; intuition.
          intuition.
          intuition.
          unfold P.transpose_neqkey.
          intuition.
          rewrite <- andb_assoc.
          rewrite <- andb_assoc.
          rewrite andb_comm with (b1:= e' =? 0).
          reflexivity.
          unfold Equal.
          intro.
          Check Z.eq_dec.
          Search ( {_ = _} + {_ <> _}).
          eelim Nat.eq_dec with (n:=y) (m:= n).
          ** intro.
            erewrite F.add_eq_o; intuition.
            erewrite F.add_eq_o; intuition.
          ** intro.
          erewrite F.add_neq_o; intuition.
          erewrite F.add_neq_o; intuition.
          erewrite F.add_neq_o; intuition.
        ++ erewrite F.add_mapsto_iff.
          intuition.
    +
    specialize (H ((NatMap.empty nat))). simpl in *.
      simpl in H.
      rewrite H.
        (* erewrite P.fold_add with (k:=n ) (e:=1) in H; intuition. *)
          erewrite P.fold_Empty in H; intuition.
          simpl in H.

        erewrite fold_1 in H.
        


      eapply elements_1 in H.
      

      elim Z.eq_dec with (x:= z1) (y:= z).
      intros.
      rewrite a.
      rewrite a0.
      specialize (H (NatMap.add n 2 (NatMap.empty nat))). simpl in *.
      rewrite a in H.
      unfold empty in H.
      re
      
      unfold elements in H.
      unfold Raw.elements in H.
      simpl in H.
      Check (Nat_as_OT.eq_refl).

      unfold Nat_as_OT.compare in H.
      
      rewrite nat_compare_eq in H.
      rewrite <- Nat.compare_refl in H.
      
      (* replace (n ?= n) with (Eq) in H; [|rewrite Nat.compare_refl with (x:=n); reflexivity]. *)
      
      simpl in H using Nat.compare_refl.
      
      rewrite <- Nat_as_OT.eq_dec in H.
    unfold empty in H. erewrite empty_1 in H.
  
 *)

 Admitted.




Require Import Program.

Lemma valid_b_more (p q : poly) (i:nat) : 
  valid_b (Poly p i q) = true -> valid_b p = true /\ valid_b q = true.
Proof.
  intro.
  split.
  induction p.
  simpl in H; intuition.
  simpl in H; intuition.
  destruct q.
  elim (Z.eq_dec z 0); intro; destruct z; intuition.
  rewrite andb_true_iff in H.
  destruct H.
  intuition.
  rewrite andb_true_iff in H.
  intuition.
  rewrite andb_true_iff in H.
  destruct H.
  rewrite andb_true_iff in H.
  destruct H.
  intuition.
  induction q.
  simpl in H; intuition.
  simpl in H; intuition.
  destruct p.
  rewrite andb_true_iff in H.
  destruct H.
  intuition.

  rewrite andb_true_iff in H.
  destruct H.
  rewrite andb_true_iff in H.
  destruct H.
  intuition.
Qed.
(* 
Lemma valid_b_moreP (p q : poly) (i:nat) : 
  valid_b (Poly p i q) = true -> valid_b p = true.
Proof.
  intro.
  
  induction p.
  simpl in H; intuition.
  simpl in H; intuition.
  destruct q.
  elim (Z.eq_dec z 0); intro; destruct z; intuition.
  rewrite andb_true_iff in H.
  destruct H.
  intuition.
  rewrite andb_true_iff in H.
  intuition.
  rewrite andb_true_iff in H.
  destruct H.
  rewrite andb_true_iff in H.
  destruct H.
  intuition.
  Qed.

Lemma valid_b_moreQ (p q : poly) (i:nat) : 
  valid_b (Poly p i q) = true -> valid_b q = true.
Proof.
  intro.
  induction q.
  simpl in H; intuition.
  simpl in H; intuition.
  destruct p.
  rewrite andb_true_iff in H.
  destruct H.
  intuition.

  rewrite andb_true_iff in H.
  destruct H.
  rewrite andb_true_iff in H.
  destruct H.
  intuition.
Qed.



Lemma valid_b_more_ (pol : poly) : 
  valid_b pol = true -> 
    match pol with 
    |Cst z => valid_b (Cst z) = true
    |Poly p i q => valid_b p = true /\ valid_b q = true
    end.
Proof.
  intro.
  destruct pol.
  assumption.
  apply valid_b_more in H.
  assumption.
Qed.


Print valid_b_more.
Check eq_rect.

Require Import Program.

Program Definition valid_b_mo_ (pol : poly) (p q:poly) (i:nat) (pr : valid_b pol = true) (preq : pol = (Poly p i q))  := _ :
valid_b (Poly p i q) = true.

Print valid_b_mo_.

Fixpoint poly_val (pol:valid_pol) (f : nat -> Z) := 
  match VP_value pol as x0 return (VP_value pol = x0) -> Z with 
  | Cst z => fun (e: (VP_value pol) = (Cst z)) => z
  | Poly p i q => 
    fun (e: (VP_value pol) = Poly p i q) =>
    let pr := valid_b_mo_ (VP_value pol) p q i (VP_prop pol) e in 
    let pr1 := valid_b_moreP p q i pr in 
    let pr2 := valid_b_moreQ p q i pr in 
    Z.add (poly_val {| VP_value := p ; VP_prop := pr1|} f) (Z.mul (f i) (poly_val {| VP_value := q ; VP_prop := pr2|}  f))
  end
  eq_refl *)

Fixpoint poly_val_ (pol:poly) (f : nat -> Z) := 
  match pol with 
  | Cst z => z
  | Poly p i q => 
    Z.add (poly_val_ p f) (Z.mul (f i) (poly_val_ p f))
end.

Definition poly_val (pol:valid_pol) (f : nat -> Z) := 
match VP_value pol with 
| Cst z => z
| Poly p i q => 
  Z.add (poly_val_ p f) (Z.mul (f i) (poly_val_ q f))
end.

Lemma val_coeff (p q : valid_pol) : (forall (f:nat -> Z), poly_val p f = poly_val q f) -> (forall (m: monoid ), get_coefficient p m = get_coefficient q m).
Proof.
  intros.
  destruct p,q.
  induction VP_value0, VP_value1.
Admitted.

