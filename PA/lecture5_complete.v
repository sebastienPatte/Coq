Require Import Arith Extraction.

Axiom todo : forall {A}, A.

(* The proof of easy_implication consists in breaking the pair of data
   stored in hypothesis {n : nat | P n = true} and to
   instantaeoulsy rebuild a new pair, with the same components,
   in a different 'container', which lands in sort Prop. *)
Lemma easy_implication (P : nat -> bool) :
{n : nat | P n = true} -> exists n, P n = true.
Proof.
  intros [n Pn].
  exists n. assumption.
Qed.

(* However the same operation does not work in the opposite
  direction, because of restricted elimination rules. *)
Lemma harder_implication (P : nat -> bool) :
  (exists n, P n = true) -> {n : nat | P n = true}.
Proof.
  Fail intros [n Pn].
Abort.

Section Markov.

(* This is what we call a boolean predicate on natural numbers. A
    witness for P is an (x : nat) for which P x = true. *)

Variable (P : nat -> bool).

(* We should not formalize the existence of a witness for P as:
   Variable (x : nat).
   Hypothesis Px : P x = true.

   This is indeed a stronger statement than the exP hypothesis
   that we use below, since it readily breaks the pair which seemed
   difficult to break in script harder above... *)

Hypothesis exP : exists n, P n = true.

(* The purpose of this exercise is to show that it is still possible
   to forge a proof term which takes benefit from exP in order to
   build an instance of the Type-sorted pair, without hitting
   the restricted elimination barrier.*)

(* The computational content of a statement asserting the
   existence of an (x : nat) such that P x = true is a search
   algorithm which terminates with outputting a natural number
   for which P x = true.*)

(* The harder statement states that from a 'non computational'
   proof (in sort Prop), possibly using a computational axiom,
   we can deduce a computational proof  (a search algorithm) that
   eventually terminates and produces a concrete and correct
   natural number. This algorithm will be the naive search
   trying natural numbers one after the other starting from 0
   and exP the justification that it terminates. We need
   to turn exP into a data we can compute on by recursion. *)

(* The structure of a proof term of the proposition
   (acc_nat i) measures the distance from i to a witness for P.
   By distance we mean the distance between i and a greater or equal
   number at which P holds. *)

(* Note that this a simplified version of the instance of the
   Acc accessiblity predicate that could also be used for
   the purpose of this proof (see next lecture). *)

(* Note that in the AccNatS constructor, we see how
   values of the parameters can be modified in the arguments of
   constructors, while being imposed in their conclusion:
   we use an (acc_nat (S i)) to build a term in (acc_nat i). *)

Inductive acc_nat (i : nat) : Prop :=
  |AccNat0 : P i = true -> acc_nat i
  |AccNatS : acc_nat (S i) -> acc_nat i.


(* The following lemma describes formally the informal intuition
   described above.  *)
(* uses plus_Snm_nSm *)
Lemma acc_nat_plus :  forall x n : nat, P (x + n) = true -> acc_nat n.
Proof.
  induction x as [|x' Hx'].
  intros.
  apply AccNat0. apply H.

  intros n' Hp.
  apply AccNatS.
  apply Hx'.
  rewrite <- plus_Snm_nSm. assumption.
Qed.

(* In particular we can use exP to show that acc_nat holds at
   0, since we carefully put the acc_nat predicate in Prop. *)
(* uses plus_0_r *)
Lemma acc_nat0 : acc_nat 0.
Proof.
  destruct exP as [n Pn].
  apply (acc_nat_plus n).
  rewrite plus_0_r. assumption.
Qed.

(* Now the main step of the proof : if acc_nat holds for an (n : nat),
   we can compute a value for which P holds. We compute
   by induction on the proof of (acc_nat n). *)
Lemma find_ex : forall n : nat, acc_nat n -> {m | P m = true}.
Proof.
fix find_ex 2.
(* we could be tempted to cheat using the seamingly correct
   correct:

   exact find_ex.
   Qed.

   but Coq complains because the proof term we just built is
   a non-terminating recursive function, of the form:
      fix f n := f n
   which cannot be accepted without risking consistency troubles... *)
intros n accn.
case (Bool.bool_dec (P n) true); intros Heq.
exists n. assumption.
apply (find_ex (S n)).
destruct accn.
- contradiction.
- apply accn.
Qed.

(* We are done: *)
Theorem Markov : {m | P m = true}.
Proof.
  eapply find_ex.
  apply acc_nat0.
Qed.

End Markov.

(* Here is the complete statement we prouved, as available outside
   of the section. *)
Check Markov.

(** A word on extraction *)
Recursive Extraction Markov.
Recursive Extraction acc_nat0.

Example nth :
  forall A (l : list A), {n : nat | n < length l} -> A.
Proof.
  intros A l n.
  induction l as [|l' Hl'].
  destruct n as [n Hn].
  - simpl in Hn.
    apply False_rect.
    red in Hn.
    Unset Printing Notations. Print le.
    inversion Hn.
    Set Printing Notations.
  - destruct n as [n Hn].
    destruct n as [|n'].
    + (* 0 *)
      exact l'.
    + (* S n' *)
      apply IHHl'.
      exists n'.
      simpl in Hn.
      apply lt_S_n. apply Hn.
Defined.

Extraction nth.

(* Exercise: nat_subterm *)

From Coq Require Import Init.Wf Relations Wellfounded.

Inductive nat_subterm : nat -> nat -> Prop :=
| nat_S_subterm x : nat_subterm x (S x).

Lemma nat_subterm_0_empty x : nat_subterm x 0 -> False.
Proof.
  intros H.
  inversion H.
Qed.

Lemma nat_subterm_wf : well_founded nat_subterm.
Proof.
  intros x.
  induction x.
  - constructor; intros y ysub. inversion ysub.
  - constructor; intros y ysub. inversion ysub; subst. exact IHx.
Qed.

Lemma nat_sub_trans_wf : well_founded (clos_trans _ nat_subterm).
Proof.
  apply wf_clos_trans, nat_subterm_wf.
Qed.

Definition fact (x : nat) : nat.
  refine
  (Fix nat_sub_trans_wf (fun _ => nat)
   (fun x fact =>
      match x as y return y = x -> nat with 
      | 0 => fun _ => 1
      | S n => fun _ => n * (fact n _)
      end eq_refl) x).
   - constructor. subst x. constructor.
Defined. 

Extraction fact.   

(* Alternative induction principles *)

Lemma alt_nat_rec (P : nat -> Prop) :
  P 0 -> (forall n, (forall m, m <= n -> P m) -> P (S n)) -> forall n, P n.
Proof.
intros P0 Pind n.
generalize (le_refl n).
generalize n at 2.
intros m.
revert n.
induction m as [|m ihm].
- intros n len0.
  apply le_n_0_eq in len0.
  now rewrite <- len0.
- intros n lenSm.
  apply Nat.le_succ_r in lenSm.
  case lenSm.
  + exact (ihm n).
  + intros enSm; rewrite enSm.
    apply Pind.
    easy.
Qed.

Section AlternateNatRecurrence.

Variable prime : nat -> Prop.
Variable div : nat -> nat -> Prop.

Hypothesis div_refl : forall n : nat, div n n.
Hypothesis prime2 : prime 2.

Hypothesis primeP : forall n : nat,
   prime n \/ exists d : nat, 2 <= d < n /\ prime d /\ div d n.

Lemma div_primeP (n : nat) : 2 <= n -> exists d, div d n /\ prime d.
Proof.
(* We first rule out cases n = 0 and n = 1 by (two) case analysis on n *)
case n as [| n].
  easy.
case n as [| n].
  now intros le21; inversion le21.
(* we mimic the proof of alt_nat_rec, strenghtening the current statement
   of the goal using appropriate generalizations. *)
generalize (le_refl n).
generalize n at 2.
intros m.
revert n.
(* now we can call the structural induction scheme. *)
induction m as [|m ihm].
- intros n len0.
  apply le_n_0_eq in len0.
  rewrite <- len0.
  intros ?; exists 2.
  now split.
- intros n lenSm le2SSn.
  case (primeP (S (S n))) as [hn | [d [? [divdSSn primed]]]].
  + now exists (S (S n)); split.
  + now exists d; split.
Qed.



End AlternateNatRecurrence.

Require Import Arith Lia.


Lemma ltb_neg_geb n m : Nat.ltb n m = negb (Nat.leb m n).
Proof.
unfold Nat.ltb. 
revert m; induction n as [|n ihn]; case m as [|m]; trivial.
exact (ihn m).
Qed.

(* This inductive definition is a technical device modeling:
 - an exclusive disjunction (two constructors)
 - in sort Set (it can be used to prove and to program)
 - with two natural number parameters
 - with two boolean indexes
 - with one extra argument for each constructor. *)

Inductive leq_xor_gtn m n : bool -> bool -> Set :=
  | LeqNotGtn : m <= n -> leq_xor_gtn m n true false
  | GtnNotLeq : n < m  -> leq_xor_gtn m n false true.

(* The purpose of this inductive definition is:
   - to model the relation between the values taken by two boolean predicates 
     depending on the parameters m and n
   - to take benefit of the unification constraints imposed by the values
     of indexes in order to automate certain substitutions and reductions 
     during the flow of a proof script. 
   - to obtain automatically some alternate, equivalent forms of 
     the boolean predicate in each branch of the case analysis, as prescribed
     by the arguments of the constructors. Here this alternate form is 
     the Prop comparison (hidden behind infix notations <= and < ). These
     can for instance be usefull for the purpose of automating proof steps
     with the omega tactic, which does not know about the boolean predicates
     NPeano.leb and NPeano.ltb. *)

(* We show the following lemma, which states in one single sentence that for
   every (n m : nat) :
   - the exclusive disjunction of (NPeano.leb m n) and (NPeano.ltb n m) holds
   - when NPeano.leb m n = true (and therefore NPeano.ltb n m = false), 
     then m <= n holds; 
   - when NPeano.leb m n = false (and therefore NPeano.ltb n m = true), 
     then n < m holds *)

Lemma leqP m n : leq_xor_gtn m n (Nat.leb m n) (Nat.ltb n m).
Proof.
(* First, we make the statement talk only about NPeano.leb: *)
rewrite ltb_neg_geb. 
(* Then we perfom a case analysis on the boolean value of (NPeano.leb m n) *)
case_eq (Nat.leb m n); intros h; simpl.
(* In each branch of the case analysis, the values of the index impose
   the constructor which can apply. *)
- constructor.
  (* We use the lemma that relates boolean and Prop formulation of the order 
    relation on nat: *)
  now apply Nat.leb_le.
- constructor.
  (* This branch requires a little bit more work: first as in the first branch, 
     we translate the goal to the Prop version: *)
  apply Nat.ltb_lt. 
  (* Then we use once again the relation we established above between the two
     boolean predicates NPeano.leb and NPeano.ltb. *)
  now rewrite ltb_neg_geb, h.
Qed.

(* The interest of this gymkhana is to limit the bureaucracy of reasonong with
   programs using case analysis on the boolean comparison predicates: *)
Section SmartCaseAnalysis.

Variable T : Type.

Variables (t1 t2 t3 : T).

Definition test1 (n m : nat) : T :=
  if (Nat.leb n m) then t1 else t2.

Lemma test1P n m : n <= m -> test1 n m = t1. 
Proof.
intros lenm.
unfold test1.
(* Now instead of the naive case_eq (NPeano.leb n m), we use our lemma: *)
case (leqP n m). 
- easy.
- intros ltmn. 
  (* The two hypothesis on n and m are contradictory. *)
  lia.
Qed.

(* A second example, with two programs test1 and test2: *)

Definition test2 (n m : nat) : T :=
  if (Nat.ltb m n) then t3 else t1.

Lemma test12P n m : n <= m -> test1 n m = test2 n m.
intros lenm.
unfold test1, test2.
(* Now instead of two naive case analysis on the (distinct) 
   if .. then .. else.. involved in the goal, we use our lemma: *)
case (leqP n m).
- easy.
- intros ltmn.
  (* The two hypothesis on n and m are contradictory. *)
  lia.
Qed.


End SmartCaseAnalysis.
