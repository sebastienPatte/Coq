Axiom LEM : forall (P:Prop), P \/ ~ P.

Axiom lDNE : forall (P:Prop), ~ ~ P -> P.

Lemma rDNE : forall (P:Prop), P -> ~ ~ P.
Proof.
	intros.
	unfold not.
	intros.
	apply H0.
	assumption.
Qed.

Lemma DNE : forall (P:Prop), P <-> ~ ~ P.
Proof.
	unfold iff; split; [apply rDNE| apply lDNE].
Qed.

Axiom CP : forall (P Q:Prop), (~ Q -> ~ P) -> P -> Q.

Lemma LEM_lDNE : (forall (P:Prop), P \/ ~ P) -> (forall (P:Prop), ~ ~ P -> P).
Proof.
	intros.
  specialize (H P).
  unfold not in H0.
  destruct H.
  - assumption.
  - specialize (H0 H).
    contradiction.
Qed.

Lemma lDNE_CP : (forall (P:Prop), ~ ~ P -> P) -> (forall (P Q:Prop), (~ Q -> ~ P) -> P -> Q).
Proof.
  intros.
  apply (H Q).
  unfold not in *.
  intros.
  apply H0.
  apply H2.
  assumption.
Qed.

Lemma nnLEM : forall (P:Prop), ~~(P \/ ~P).
Proof.
  intros.
  unfold not.
  intro.
  apply H.
  right.
  intro.
  apply H.
  left.
  assumption.
Qed.

Lemma CP_LEM : (forall (P Q:Prop), (~ Q -> ~ P) -> P -> Q) ->  (forall (P:Prop), P \/ ~ P).
Proof.
  intro.
  unfold not in *. intros P. 
Abort.

Lemma A_LEM (A: Prop -> Prop) : forall (P:Prop), (A P) \/ ~ (A P).
Abort.

Lemma sig1 (P:Prop) : exists (d: nat -> bool), P <-> (exists (n:nat), d n =true).
Proof.
Abort.

(** Axiom Of Choice **)

(* Inductive inhabited (Y:Type) : Prop :=   *)

(* Lemma AC00 (X : Type) (R: X -> Type):
  (forall (x:X), inhabited (R x)) -> 
  (exists (d: X -> Y), forall (x:X), R x (d x)).
Proof.
Abort. *)

Lemma AC (X Y : Type) (R: X -> Y -> Prop):
  (forall (x:X), exists (y:Y), R x y) -> 
  (exists (d: X -> Y), forall (x:X), R x (d x)).
Proof.
Abort.

(** Extentionality **)
Definition vector (A:Type) (n:nat) : Type := {l : list A| length l = n }.

Require Import List.
Import ListNotations.


Check ({_ | length [5] = 1} ). 

Lemma univalence (X Y : Type) :
  forall (f:X->Y), forall (g:Y->X),
  (forall (x:X), g (f x) = x) ->
  (forall (y:Y), f (g y) = y) ->
  X = Y.
Proof.
  intros.
    