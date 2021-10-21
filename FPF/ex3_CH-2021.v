
(* In Coq, propositions are of type Prop, which means they are types. *)
(* Data-types are of type Type or Set, which means they are also types  *)
(* The differences between Prop, Set and Type will be made clear later *)


(* ex 1 *)

Definition easy : forall P : Prop, P -> P :=
  fun X (x:X) => x.
Print easy.

(* In Coq, -> is just a particular case of forall *)
Check forall n : nat, True.

(* Minimal logic *)
Parameter A B C : Prop.

(* Prove *)
Definition e1 : 
  A -> A :=...

Definition e2 : 
  (A -> B) -> (B -> C) -> A -> C :=
...

Definition e3 : 
  A -> B -> A :=
...

Definition e4 : 
  (A -> B -> C) -> (A -> B) -> A -> C :=
...


(* Negation : remember ~A is an abrevation for A -> False *)
(* Prove the following, possibly using False_ind *)
Definition e5 : A -> ~~A :=
...

Definition e6 :       
  (A -> B) -> (~B -> ~A) :=
...

Definition e7 : 
  ~~(~~A -> A) :=
...



(* forall quantification *)
Parameter P Q R: A -> Prop.

Definition e8 : 
  (forall x, P x -> Q x) -> (forall x, P x) -> (forall x, Q x)
  := ...

Definition e9 : 
  (forall x, P x -> Q x) -> (forall x, Q x -> R x) -> (forall x, P x -> R x) := ...

Parameter f : A -> A.
Parameter c : A.

Definition e10 :
  (forall x , P x -> P (f x)) -> (forall x, P x -> P (f(f x))) :=  ...

Definition e11 :
  (forall x, P x -> Q x) -> ~Q c -> ~(forall x, P x)  :=
...

(* existantial quantification *)
Check ex_intro.

(* Possibly use @ex_intro instead of ex_intro to prevent
  the system to guess implicit arguments *)

Definition al_ex : forall A : Type, forall P : A -> Prop,
      A -> (forall x, P x) -> (exists x, P x) :=
...  

Definition ex_al : forall A : Type, forall P : A -> Prop,
      ~(exists x, P x) -> forall x, ~(P x) :=
...


(* Induction  / recursion *)
Definition half x y :=  x=y+y \/ x = S (y+y).

Definition d (x:nat) := exists y,half x y.


(* advanced : do the following without tactics ! *)
(* for now, just use it *)
Lemma dS : forall x, d x -> d(S x).
Proof.
intros x dx.
destruct dx as [y [ey|ey]].
exists y; right.
rewrite ey; trivial.
exists (S y); left.
rewrite <- plus_n_Sm, ey.
simpl; trivial.
Defined.


(* this one is easier without tactics *)
Definition d0 : (d 0).
...
Defined.

(* For writing the proof-terms explicitly, you
  may check the types of or_introl, or_intror and 
  refl_equal.

(* Here you build a recursive proof as a term - 
  this will be studied next week *)
Fixpoint dn (n : nat) : (d n) :=
  match n with
    0 => ...
  | (S m) => ...
  end.

Eval compute in (dn 3).


