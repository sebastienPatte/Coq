
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
 A -> A := fun a => a.
Definition e2 : 
  (A -> B) -> (B -> C) -> A -> C :=
  fun ab bc a => bc (ab a).
Definition e3 : 
  A -> B -> A :=
  fun a b => a.
Definition e4 : 
  (A -> B -> C) -> (A -> B) -> A -> C :=
  fun abc ab a => abc a (ab a).


(* Negation : remember ~A is an abrevation for A -> False *)
(* Prove the following, possibly using False_ind *)
Definition e5 : A -> ~~A :=
   fun a na => na a.


Definition e6 :       
  (A -> B) -> (~B -> ~A) :=
  fun ab nb a => (nb (ab a)).

Definition e7 : 
  ~~(~~A -> A) :=
  fun naa : ~(~~A -> A)  => naa
                              (fun na : ~~A =>
 False_ind A (na (fun a =>  (naa (fun _ => a) )))).
                                 


(* forall quantification *)

Parameter P Q R: A -> Prop.
Definition e8 : 
  (forall x, P x -> Q x) -> (forall x, P x) -> (forall x, Q x)
  :=
    fun apq ap x => (apq x (ap x)).

Definition e9 : 
  (forall x, P x -> Q x) -> (forall x, Q x -> R x) -> (forall x, P x -> R x) :=
fun apq aqr x px => (aqr x (apq x px)).

Parameter f : A -> A.
Parameter c : A.
Definition e10 :
  (forall x , P x -> P (f x)) -> (forall x, P x -> P (f(f x))) :=
fun appf x px => (appf (f x) (appf x px)).

Definition e11 :
  (forall x, P x -> Q x) -> ~Q c -> ~(forall x, P x)  :=
  fun apq nqc apx => nqc (apq c (apx c)).


(* existantial quantification *)
Check ex_intro.

Definition al_ex : forall A : Type, forall P : A -> Prop,
      A -> (forall x, P x) -> (exists x, P x) :=
fun A P a ap => (@ex_intro A P a (ap a)).
  

Definition ex_al : forall A : Type, forall P : A -> Prop,
      ~(exists x, P x) -> forall x, ~(P x) :=
  fun A P nex x px => (nex (@ex_intro A P x px)).


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

Definition d0 : (d 0).
 exists 0.
 left.
 reflexivity.
Defined.

Fixpoint dn (n : nat) : (d n) :=
  match n with
    0 => d0
  | (S m) => (dS m (dn m))
               end.

Eval compute in (dn 3).