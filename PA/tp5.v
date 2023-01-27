Definition and_ (P Q : Prop) := 
	forall R:Prop, P -> Q -> R
.


Definition or_ (P Q : Prop) := 
	forall R:Prop, (P -> R) -> (Q -> R) -> R
.

Eval compute in (and_ True False).

Print or.

Definition ex_ {X} (P : X -> Prop) := 
	forall R:Prop, (forall x, P x -> R) -> R
.

Goal forall X (P:X -> Prop), ex P <-> ex_ P.
Proof.
  intros.
  unfold iff.
  split.
  - intro. 
    unfold ex_.
    intros.
    destruct H.
    specialize (H0 x).
    apply (H0 H).
  - unfold ex_.
    intros.
    apply H.
    intros.
    exists x.
    assumption.
Qed.

Definition nth {A} (l: list A) : {n:nat | n < length l} -> A.
Proof.
  induction l.
  - simpl. intros [n H]. eapply False_rect. inversion H.
  - simpl. intro. destruct H. assumption. 
Defined.
    
Require Import Extraction.
Extraction Language OCaml.
Extraction nth.
Extract Inductive nat => "int" ["0" "succ"].

Variable f: nat -> bool.

(* Goal (exists n, f n = true) -> {n | f n = true}.
Proof.
  intros.
   *)

Section Acessibility.
Variables (A:Set) (R: A -> A -> Prop).
Lemma not_Acc (a b:A) : R a b -> Acc R a -> Acc R b.
Proof.
  intros.
  destruct H0.
  apply H0.
  
  

Print Acc.

End Acessibility.