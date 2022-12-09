(* Universe hierarchy *)

Check Type.

Set Printing Universes.

Check Type.

Universes i j.

Fail Constraint i < Set.
Fail Constraint i = Set.

Constraint i < j.

Check Type@{i} : Type@{j}.

Fail Check Type@{j} : Type@{i}.

Check Type@{i} -> Type@{i}.

Check ((forall (P : Prop), nat -> P) : Prop).

Check ((forall (A : Type), A -> False) : Prop).

Fail Check ((forall (A : Type), A -> Empty_set) : Set).

Universes k l.

Check ((forall (A : Type@{k}), A -> Empty_set) : Type@{l}).

(** Type eliminations *)

Section TypeElim.
  Variable b : bool.

  Check (match b return Type with
         | true => nat
         | false => bool
         end).

  Check (match b return Prop with
         | true => True
         | false => False
         end).

  Check (match b return (nat : Set) with
         | true => 0
         | false => 1
         end).

End TypeElim.

(** Prop eliminations *)
Section PropElim.
  Variable P : Prop.
  Variable b : or P P.

  Fail Check (match b return Type with
              | or_introl _ => nat
              | or_intror _ => bool
              end).

  Fail Check (match b return Prop with
         | or_introl _ => P
         | or_intror _ => P
         end).

  Fail Check (match b return (nat : Set) with
         | or_introl _ => 0
         | or_intror _ => 1
         end).

  Check (match b return P with
         | or_introl p => p
         | or_intror p => p
         end).

End PropElim.

Section PropSingleton.
  Variable b : (True : Prop).

  Check (match b return Type with
              | I => nat
              end).

  Check (match b return Prop with
         | I => False
         end).

  Check (match b return (nat : Set) with
         | I => 0
         end).

  Check (match b return True with
         | I => I
         end).

End PropSingleton.

Section PropSingletonEq.
  Variables (A : Type) (x y : A).
  Variable b : (@eq A x y : Prop).

  Check (match b return Type with
              | eq_refl => nat
              end).

  Variable (P : A -> Type).

  Check (match b in eq _ y return P y -> P x with
         | eq_refl => fun x : P x => x
         end).

End PropSingletonEq.

Section PropExElim.
  Variables (A : Type) (P : A -> Prop).
  (* [exist x : A, P x] is a notation for [ex A P]
     where: 

     Inductive ex (A : Type) (P : A -> Prop) : Prop :=
       ex_intro : forall x : A, P x -> exists y, P y  
  *)
  Fail Definition project (e : exists x : A, P x) : A :=
    match e return A with
    | ex_intro _ witness proof => witness
    end.
    
  (* [{ x : A | P x} is a notation for [sig A P] where:
  
  Inductive sig (A : Type) (P : A -> Prop) : Type :=
	exist : forall x : A, P x -> {x : A | P x}
  *)
  Definition project (e' : { x : A | P x }) : A :=
   match e' return A with 
      | exist _ witness proof => witness
   end.
End PropExElim.

Require Import Arith.

Inductive collatz : nat -> Set :=
| collatz_terminates : collatz 1
| collatz_0 n : n mod 2 = 0 -> collatz (n / 2) -> collatz n
| collatz_1 n : n mod 2 = 1 -> collatz (3 * n + 1) -> collatz n.

Fixpoint collatz_steps {n : nat} (c : collatz n) : nat :=
  match c with
  | collatz_terminates => 0
  | collatz_0 n _ c => S (collatz_steps c)
  | collatz_1 n _ c => S (collatz_steps c)
  end.

Inductive squash (A : Type) : Prop := 
| sq : A -> squash A.

Axiom collatz_conjecture: forall n, squash (collatz n).

(** Elimination restrictions ensure "irrealizable" axioms in [Prop] do not endanger the 
    computations in Type. E.g. we cannot get "non-standard" numbers.
*)

Fail Definition collatz_steps_of (n : nat) : nat :=
  match collatz_conjecture n with
  | sq _ collatzn => collatz_steps collatzn
  end.

  
