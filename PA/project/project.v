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
| (Poly p1 j1 q1), (Cst _) => 
	Nat.ltb i j1 
  && valid_bool p 
| (Cst _),  (Poly p2 j2 q2) => 
	Nat.leb i j2 
  && valid_bool q 
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


  
Lemma all_coeff_eq (p q : valid_pol) : (forall (m : monoid), get_coefficient p m = get_coefficient q m) -> p = q.
Proof.


  unfold get_coefficient.
  destruct p,q.
  simpl.
  intro.
  apply leibniz.
  (* induction VP_value0, VP_value1; simpl in *. *)

  induction VP_value0; induction VP_value1; simpl; simpl in H.

  - specialize (H empty_mono). simpl in H. f_equal. assumption.
  - inversion VP_prop1.
    replace VP_value1_1 with (Cst z) in IHVP_value1_1.
    specialize (IHVP_value1_1 VP_prop0).
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
      simpl in IHVP_value1_1.
      
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
  
