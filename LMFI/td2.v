
(** TD1 *)

Set Universe Polymorphism. (* Indispensable pour [church_minus] (Exo 3) *)

(** Exo 1 *)

Definition compose {A B C} (f:B->C)(g:A->B) := fun x => f (g x).

Compute compose S pred 7.
Compute compose S pred 0.
Compute compose pred S 0.

(** Exo 2 *)

Definition mybool := forall X, X->X->X.

Definition mytrue : mybool := fun _ x y => x.
Definition myfalse : mybool := fun _ x y => y.

Definition myif : forall {Y}, mybool -> Y -> Y -> Y :=
 fun _ b x y => b _ x y.

Compute myif mytrue 0 1.
Compute myif myfalse 0 1.

(** Exo 3 *)

Definition church := forall X, (X->X)->(X->X).

Definition zero : church := fun _ f x => x.
Definition one : church := fun _ f x => f x.
Definition onebis : church := fun _ f => f.
Definition two : church := fun _ f x => f (f x).

Definition succ : church -> church :=
 fun n => fun _ f x => n _ f (f x).

Compute succ one.

Definition church2nat (n:church) := n _ S 0.

Compute church2nat zero.
Compute church2nat one.
Compute church2nat onebis.
Compute church2nat two.

Fixpoint nat2church (n:nat) :=
 match n with
 | O => zero
 | S m => succ (nat2church m)
 end.

Compute nat2church 3.
Compute church2nat (nat2church 100).

Definition church_plus (n m:church) : church :=
  fun _ f x => n _ f (m _ f x).

Compute church_plus one two.
Compute church2nat (church_plus (nat2church 13) (nat2church 10)).

Definition church_mult (n m:church) : church :=
 fun _ f =>  n _ (m _ f).

Compute church_mult one two.
Compute church2nat (church_mult (nat2church 13) (nat2church 10)).

Definition church_pow (n m:church) : church :=
 fun _ =>  m _ (n _).

Compute church_pow two two.
Compute church2nat (church_pow (nat2church 2) (nat2church 5)).

Definition is_zero (n : church) : bool :=
  n _ (fun _ => false) true.

Compute is_zero zero.
Compute is_zero one.

Compute church.

Definition church_pred (n:church) : church :=
 fun _ f x =>
   n _ (fun g h => h (g f)) (fun _ => x) (fun u => u).

Fail Compute (church church).

Compute church2nat (church_pred zero).
Compute church2nat (church_pred one).
Compute church2nat (church_pred (nat2church 13)).

(** Attention, donne [universe inconsistency] si les univers
    polymorphes ne sont pas activés. *)

Definition church_minus (n m : church) : church :=
  m _ church_pred n.

Definition f (x:False) : False := x.

Inductive bool :=
|true : bool
|false : bool.

Compute bool_rect. 

Fail Inductive t :=
|c1 : (t -> t) -> t.


Compute church2nat (church_minus two two).
Compute church2nat (church_minus (nat2church 10) (nat2church 7)).


(** Exo 4 *)

Open Scope bool_scope.

Definition checktauto f := f true && f false.
Definition checktauto2 f := checktauto (compose checktauto f).
Definition checktauto3 f := checktauto (compose checktauto2 f).

Compute checktauto3
        (fun a b c => a || b || c || negb (a && b) || negb (a && c)).
Compute checktauto3 (fun a b c => a || b || c).

(** A revoir lors du cours sur les "types dépendants" :
    une généralisation de checktauto aux fonctions booléennes
    à n arguments. P.ex. nbool 2 = bool -> bool -> bool
    Et nchecktauto 2 se comportera comme le checktauto2 précédent. *)

Fixpoint nbool n :=
 match n with
 | 0 => bool
 | S n => bool -> nary n
 end.

Fixpoint nchecktauto n : nbool n -> bool :=
 match n with
 | 0 => fun b => b
 | S n => fun f => nchecktauto n (f true) && nchecktauto n (f false)
 end.

Compute nchecktauto 3
        (fun a b c => a || b || c || negb (a && b) || negb (a && c)).
Compute nchecktauto 3 (fun a b c => a || b || c).



(** Exo 5 *)

Require Import Arith.

Fixpoint add n m :=
 match n with
 | 0 => m
 | S n => S (add n m)
 end.

Compute add 3 7.

Fixpoint mul n m :=
 match n with
 | 0 => 0
 | S n => add m (mul n m)
 end.

Compute mul 3 7.

Fixpoint sub n m :=
 match n, m with
 | _,0 => n
 | 0,_ => n
 | S n, S m => sub n m
 end.

Compute sub 7 3.
Compute sub 3 7.

Fixpoint fact n :=
 match n with
 | 0 => 1
 | S m => mul n (fact m)
 end.

Compute fact 8.

Fixpoint pow a b :=
 match b with
 | 0 => 1
 | S b => mul a (pow a b)
 end.

Compute pow 2 10.

(* En Coq 8.4, ajouter:
Require Import NPeano.
Infix "=?" := Nat.eqb (at level 70, no associativity) : nat_scope.
*)

Fixpoint modulo_loop a b n :=
 match n with
 | 0 => 0
 | S n =>
   if a <? b then a
   else modulo_loop (sub a b) b n
 end.

Definition modulo a b := modulo_loop a b a.

Compute modulo 10 3.
Compute modulo 3 0.

Fixpoint gcd_loop a b n :=
  match n with
  | 0 => 0
  | S n =>
    if b =? 0 then a
    else gcd_loop b (modulo a b) n
  end.

Definition gcd a b := gcd_loop a b (S b).

Compute gcd 17 23.
Compute gcd 23 17.
Compute gcd 12 9.
Compute gcd 9 12.
Compute gcd 10 1.
Compute gcd 1 10.
Compute gcd 0 7.
Compute gcd 7 0.

(* ---------------------------------------- *)
Require Import List.
Import ListNotations.
Check [].