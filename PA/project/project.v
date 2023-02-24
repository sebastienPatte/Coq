Require Import definitions.
Import F P NatMap FMapList.
Definition empty : monoid := NatMap.empty nat.

Require Import PolyArith Coeff PolyVal. Import Equations.

Require Import Valid.
Require Import ZArith Arith Bool Lia.
Require Import BoolHelp Maps.

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