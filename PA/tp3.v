(* 1.1 *)

Definition negb (b: bool) := if b then false else true.

Definition andb (b1 b2: bool) := if b1 then b2 else false.

Eval compute in  (fun x:bool => negb (andb false x)).
Eval compute in  (fun x:bool => negb (andb x false)).

(* 1.2 *)

Parameter (A B : Type) (t1:A) (t2:B).

Fail Definition g {A B} (b:bool) := match b with true => t1 | false => t2 end.

Definition g (b:bool)  := 
	match b return (if b then A else B) with true => t1 | false => t2 
end.

Eval compute in (g true).
Eval compute in (g false).

Definition g2 (b:bool) := 
	match negb b as b0 return (if b0 then B else A) with true => t2 | false => t1 
end.

(* 1.3 *)

Inductive even : nat -> Prop :=
| even0 : even 0
| evenS n : even n -> even (S (S n)).

Lemma even_is_double : forall n, even n -> exists m, n=m+m.
Proof.
	intros.
	induction H.
	- exists 0.
	  intuition.
	- destruct IHeven.
	  exists (S x).
	  rewrite H0.
    simpl.
    intuition.
Qed.

Lemma even_is_double' : forall n,
(even n -> exists m, n=m+m) /\ (even (S n) -> exists m, n=S(m+m)).
Proof.
  intro.
  induction n; split; intro.
  - exists 0. intuition.
  - inversion H.
  - destruct IHn.
    specialize (H1 H).
    destruct H1.
    exists (S x).
    simpl.
    rewrite H1.
    intuition.
  - destruct IHn.
    inversion H.
    specialize (H0 H3).
    destruct H0.
    exists (x).
    f_equal.
    assumption.
Qed.
    
Require Import List.
Import ListNotations.

Fixpoint belast (x:nat) (l: list nat) : list nat := 
  match l with 
  |[] => []
  |y::l => x::(belast y l)
  end.

Lemma length_belast (x : nat) (s : list nat) : length (belast x s) = length s.
Proof.
  revert x.
  induction s.
  - unfold belast. reflexivity.
  - intro. 
    simpl.
    specialize (IHs a). 
    f_equal.
    assumption.
Qed.

Fixpoint skip (l : list nat) : list nat := 
  match l with 
  |x::(y::ll) => x:: skip (ll)
  |_=> l
end.

Parameter (x y z : nat).
Eval compute in (skip [x;y;z]).
Eval compute in (belast y (skip [x;y;z])).

Require Import Lia.

Lemma length_skip :
forall l, 2 * length (skip l) <= length l.
Proof.
  intro.
  induction l. 
  - simpl. trivial.
  - destruct l; intuition. lia.
     

