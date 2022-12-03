
Inductive and (A:Prop) (B:Prop) : Prop :=
| conj : A -> B -> and A B.

Check (and_ind).

Inductive True : Prop := I.
Check (True_ind).

Inductive False : Prop := .
Check (False_ind).
Check (O).

Definition prf : 3 * 3 = 9 := eq_refl.

Lemma prf_q1 : 3 * 3 = 9 .
Proof.
reflexivity.
Qed.

Inductive aexpr (N : Type) :=
 | cst : N -> aexpr N
 | var : nat -> aexpr N
 | add : aexpr N -> aexpr N -> aexpr N.

 Check cst.
Fixpoint  aexpr_elim 
 (P:Type) (N : Type) 
 (Pcst : N -> P)
 (Pvar : nat -> P) 
 (Padd : aexpr N -> P -> aexpr N -> P -> P) 
 (exp : aexpr N)
:=
match exp with 
|cst _ n => Pcst  n
|var _ v => Pvar  v
|add _ e1 e2 => Padd e1 (aexpr_elim P N Pcst Pvar Padd e1) e2 (aexpr_elim P N Pcst Pvar Padd e2)
end.







Inductive ex (A:Type)(P:A->Prop) : Prop :=
| ex_intro : forall (x:A), P x -> ex A P.

Check ex_ind.

Unset Elimination Schemes.

Inductive even : nat -> Prop :=
| E0 : even 0
| ESS (n:nat) (e:even n) : even (S (S n)).

Set Elimination Schemes.
Scheme even_ind := Induction for even Sort Prop.   


Check even_ind.
Eval compute in even_ind.




Scheme eq_ind_dep := Induction for eq Sort Prop.

Eval compute in eq_ind_dep.

Definition pred (n:nat) :=
  match n with O => O | S k => k end.
Check f_equal pred.
Eval compute in f_equal.


Inductive e (A:Type) : Type := C (_:A).
Eval compute in e_ind.

Definition aaaa := fix F (n:nat) := n.
Check aaaa 0.

Inductive i1 : Type := c1 : i1 -> i1.
(*Inductive i2 : Type := c2 : (i2 -> bool) -> i2.*)
Inductive i3 : Type := c3 : (i1 -> bool) -> i3.
Definition f1 : Prop := forall p : Prop, p \/ ~ p.
(*Definition f2 : Set := forall A : Set, list A -> nat.*)
Definition f3 : Type := forall A : Set, list A -> nat.


Check forall A : Type, list A -> nat.

Inductive nat : Set :=
| O : nat
| S : nat -> nat.

Check forall A : Type, list A -> nat.

Definition even_ind_dep 
  (P : forall n : nat, even n -> Prop)
  (h0 : P 0 E0)
  (hSS : forall (n : nat) (e : even n), P n e -> P (S (S n)) (ESS n e))
:=  
  fix F (n : nat) (e : even n) : P n e :=
  match e as e0 in (even n0) return (P n0 e0) with
  | E0 => h0
  | ESS n0 e0 => hSS n0 e0 (F n0 e0)
  end
.

Check even_ind_dep.
Inductive iff (A:Prop) (B:Prop) : Prop :=
| iff_i : (A -> B) -> (B -> A) -> iff A B.

(*Check iff_ind.
Eval compute in iff_ind.*)

Set Elimination Schemes.
Scheme iff_rectd := Induction for iff Sort Prop.   

Check iff_rectd.
Eval compute in iff_rectd.

Definition iff_rect_dep (A B : Prop)
  (P : iff A B -> Type)
  (f: forall (a : A -> B) (b : B -> A), P (iff_i A B a b))
  (i : iff A B)
  :=
  match i  return (P i) with 
  | iff_i _ _ a' b' => f a' b'
  end
.

Eval compute in iff_rect_dep.

(*
   forall (A B : Prop) (P : iff A B -> Type),
  (forall (a : A -> B) (b : B -> A), P (iff_i A B a b)) ->
   forall i : iff A B, P i
*)

Inductive vect (A:Type) : nat -> Type :=
| niln : vect A O
| consn : A -> forall n:nat, vect A n -> vect A (S n).

Eval compute in vect_ind.

Definition vect_ind_bis 
	(A : Type) 
	(P : forall n : nat, vect A n -> Prop)
	(fniln : P 0 (niln A))
	(fconsn : forall (a : A) (n : nat) (v : vect A n), P n v -> P (S n) (consn A a n v)) 
  :=
  fix F (n : nat) (v : vect A n) : P n v :=
  match v as v0 in (vect _ n0) return (P n0 v0) with
  | niln _ => fniln
  | consn _ y n0 v0 => fconsn y n0 v0 (F n0 v0)
  end.


Check vect_ind_bis.

Inductive tuple (A:Type) :=
| C0 : A -> tuple A
| CS : tuple (A*A) -> tuple A.

Eval compute in tuple_rect.

Definition cbtree_ind_bis 
  (P : forall A : Type, cbtree A -> Prop)
  (f : forall (A : Type) (a : A), P A (C0 A a))
  (f0 : forall (A : Type) (c : cbtree (A * A)), P (A * A)%type c -> P A (CS A c)) 
  :=
       fix F (A : Type) (c : cbtree A) {struct c} : P A c :=
         match c as c0 return (P A c0) with
         | C0 _ y => f A y
         | CS _ c0 => f0 A c0 (F (A * A)%type c0)
         end.

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
(* 
Parameter (A : Type@{i}).
Parameter (B: A -> Type@{i}).

Check ((forall (x:A), B x) ).
Check (Type@{i} -> Type@{i}).
 *)

Check(Type@{i}).
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

  

