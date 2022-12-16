Require Import Arith.

Axiom todo : forall A, A.
Ltac todo := apply todo.

Goal True.
  exact I.
Qed.

Check True.

Print Module Init.Nat.

Parameter A B C : Prop.

Lemma AimpA : A -> A.
Proof.
  intro.
  assumption.
Qed.

Lemma imp_trans : (A -> B) -> (B -> C) -> A -> C.
Proof.
  intros.
  apply H0.
  apply H.
  assumption.
Qed.

Lemma and_comm : A /\ B -> B /\ A.
Proof.
  intro.
  destruct H.
  split; assumption.
Qed.

Lemma or_comm : A \/ B -> B \/ A.
Proof.
  intro.
  destruct H; [right | left]; assumption.
Qed.

Lemma A_imp_nnA : A -> ~~A.
Proof.
  unfold not.  
  intros.
  apply H0.
  assumption.
Qed.

Lemma distr_and_or : (A\/B)/\C -> A/\C \/ B/\C.
Proof.
  intros.
  destruct H. 
  destruct H. 
  + left. split; assumption.
  + right. split; assumption.
Qed.

Lemma equiv_refl : A <-> A.
Proof.
  unfold iff.
  split; intro; assumption.
Qed.

(** 2.2 Classical logic *)

Lemma equiv_classic :
  (forall P, P \/ ~P) <-> (forall P, ~~P -> P).
Proof.
  unfold iff. 
  split; unfold not; intros.  
  - destruct H with P. 
    + assumption.
    + apply H0 in H1. contradiction.
  - apply H.
    intro.
    apply H0.
    right.
    intro.
    destruct H0; left; assumption.
Qed.

(* 2.2.1 {Classical formulae in an intuitionistic world *)
(* Modelization of a definition and lemmas *)

Definition is_classical (P:Prop) := ~~P -> P. 

Lemma nn_funct (P Q : Prop) : ~~ P /\ (P -> Q) -> ~~Q.
Proof.
  unfold not.  
  intro.
  
  destruct H.
  intro. 
  apply H1.
  apply H0. 
  destruct H.
  intro.
  apply H1.
  apply H0.
  assumption.
Qed.

Lemma class_t : is_classical True.
Proof.
  unfold is_classical.
  unfold not.
  intro.
  trivial.
Qed.
  
Lemma class_f : is_classical False.
Proof.
  unfold is_classical.
  unfold not.
  intro.
  destruct H.
  intro.
  assumption.
Qed.

Lemma class_conj (P Q : Prop) : is_classical P /\ is_classical Q -> is_classical (P /\ Q).
Proof.
  unfold is_classical.
  unfold not.
  intro.
  destruct H.
  intro.
  split.
  - apply H.
    intro.
    apply H1.
    intro.
    destruct H3. apply H2. apply H3.
  - apply H0.
    intro.
    apply H1.
    intro.
    destruct H3. apply H2. apply H4.
Qed.  



(* 3.1 Socrates *)
(* Modelization using axioms *)
Parameter Person:Type.
Parameter Socrate : Person.
Parameter Men Mortal : Person->Prop.

Lemma socrateMortal : Men Socrate /\ (forall P:Person, Men P -> Mortal P) -> Mortal Socrate.
Proof.
  intro.
  destruct H.
  apply H0 in H.
  assumption.
Qed.

Print socrateMortal.

(* 3.2 Drinkers paradox *)
(* Modelization using axioms + classical logic *)
Parameter EM : forall P, ~~ P -> P.

Lemma drinker : exists p:Person, ~ Mortal p -> forall q:Person, ~ (Mortal q).
Proof.
  apply EM.
  intro.
  apply H.
  exists Socrate.
  intros.
  intro.
  apply H.
  exists q.
  intro.
  contradiction.
Qed.

(* 3.3 Equality *)

(* Example *)

Goal forall x y : nat, x = S y -> y = pred x.
Proof.
  intros x y e.
  rewrite e. 
  simpl.
  reflexivity.
Qed.

(* Require Import Classical.
Check NNPP. *)

(* 3.4 Groups *)
(* Modelization using axioms + equational reasoning using rewrite/reflexivity/symmetry/transivitity *)

Parameter (G:Type).
Parameter op : G -> G -> G.
Parameter inv : G -> G.
Parameter e : G.

Axiom assoc  : forall (a b c : G),  op (op a b)  c = op a  (op b c).
Axiom id_l : forall (a: G), op a e = a.  
Axiom id_r : forall (a: G), op e a = a.

Axiom inv_r : forall (a:G), op a (inv a) = e.
Axiom inv_l : forall (a:G), op (inv a) a = e.

Lemma group (x y:G) : inv (op x y) = op (inv y) (inv x).
Proof.
  transitivity (op (inv y) (op (inv x) (op (op x y) (inv (op x y))))).
  - rewrite assoc.
    rewrite <- assoc with (a:=inv x) (b:=x).
    rewrite inv_l.
    rewrite id_r.
    rewrite <- assoc.
    rewrite inv_l.
    rewrite id_r.
    reflexivity.
  
  - rewrite inv_r.
    rewrite id_l.
    reflexivity.
Qed.

