(* Socrate is a men, all mens are mortal, therefore socrate is mortal *)

Parameter Person:Type.
Parameter Socrate : Person.
Parameter Men Mortal : Person->Prop.

Lemma socrateMortal : Men Socrate /\ (forall P:Person, Men P -> Mortal P) -> Mortal Socrate.
Proof.
	intros.
	destruct H.
	apply H0 in H.
	apply H.
	Show Proof.
Qed.

Definition sym (A:Type) (x y:A) (e:x=y) : y=x :=
	@eq_ind A x (fun a => a=x) eq_refl y e
.

Check eq_ind.
Check sym.


Definition trans (A:Type) (x y z:A) (e1: x=y) (e2 : y=z) : x=z :=
	@eq_ind A y (fun a => x = a) e1 z e2
.

Check trans.


Definition cong (A B:Type) (f: A -> B) (x y :A) (e: x=y) : f x = f y :=
	@eq_ind A x (fun a => f x = f a) eq_refl y e
.
Check cong.

Check eq_rect.

Definition congd (A :Type) (B:A->Type) (f: forall x:A,B x) (x y :A) (e: x=y) : 		(@eq_rect A x B (f x) y e ) = f y
.
Proof.
	destruct e.
	compute.
	reflexivity.
Qed.

Check Prop.
Check Type.
Check Prop -> Prop.
Check forall (P:Prop), P.
Check forall (P:Type), P.

Definition t := Type.
Check t.

Fail Check (forall (P:t), P) : t. 
Definition p := Prop.
Check (forall (P:p), P) : p.

Definition conj (A B : Prop) := forall Q:Prop, (A->B->Q)->Q.

Definition conj_i (A B : Prop) (h1 : A) (h2 : B) : conj A B :=
	fun Q f => f h1 h2
.


Check conj_i.

(*exam 2017*)

Definition t1 : { x : nat | x = 3 } := 
	 exist _ 3 eq_refl
.

Eval compute in eq_sym.

Definition eq_sym {A : Type} (x y : A) (e : x = y) : y = x :=
match e in _ = _ return _ with
| eq_refl => eq_refl
end.


Check True.
Check unit.

Check True_ind.
Check unit_ind.

Check and.
Check prod.

Check and_ind.
Check prod_ind.

Check sig.
Check ex.

Check sig_ind.
Check ex_ind.

Example nth : forall A (l : list A),
{n : nat | n < length l} -> A.
Admitted.

(*exam*)

Inductive tree : Type := 
|L : nat -> tree 
|N : nat -> tree -> tree -> tree.

Fixpoint mult (t:tree) : nat :=
match t with 
|L n => n
|N n ln rn => 
	n * (mult ln) * (mult rn) 
end.

Eval compute in (mult (N 2 (L 3) (L 2))).

Fixpoint in0 (t:tree) : Prop :=
match t with
|L 0 => True
|L _ => False
|N 0 _ _ => True
|N _ ln rn => (in0 ln) \/ (in0 rn)
end.

Eval compute in (in0 (N 2 (L 3) (L 2))).
Eval compute in (in0 (N 2 (L 3) (L 0))).

Inductive inO : tree -> Prop :=
| inO_L : inO (L O)
| inO_N l r : inO (N O l r)
| inO_N_l n l r : inO l -> inO (N n l r)
| inO_N_r n l r : inO r -> inO (N n l r).

Eval compute in (in0 (N 2 (L 3) (N 6 (L 0) (L 1)))).
Eval compute in (inO (N 2 (L 3) (N 6 (L 0) (L 1)))).
Eval compute in (inO (N 2 (L 3) (N 6 (L 2) (L 1)))).



Definition unit {A} : A -> option A := Some.
Definition bind {A B} (m : option A) (f : A -> option B) : option B :=
match m with
| Some x => f x
| None => None
end.
Definition raise {A} : option A := None.


Fixpoint mult0 (t : tree) : option nat :=
match t with
| L 0 => raise
| L n => unit n
| N 0 l r => raise
| N n l r =>
	bind (mult0 l) (fun l' => 
	bind (mult0 r) (fun r' => 
		unit (n * l'* r')
	))
end.

Eval compute in (mult (N 2 (L 3) (L 2))).
Eval compute in (mult0 (N 2 (L 3) (L 2))).
Eval compute in (mult0 (N 2 (L 3) (L 0))).

Definition M (A : Type) :=
  forall (C : Type), (A -> C) -> C -> C 
.

Definition unit' {A} (a:A) : M A :=
	fun _ f _ => f a 
.

Check unit'.

Definition raise' {A} (a:A) : M A :=
	fun _ _ x => x 
.

Definition bind' {A B}  ( ma : M A) (f : A -> M B) : M B :=
	fun c sk fk => ma c (fun a => f a c sk fk) fk
.

Check bind'.

Definition catch {A}  (e1 : M A) (e2 : A) : A := 
	e1 A (fun a => a) e2 
.

(***)

Parameter epsilon : forall (A:Type), A -> (A -> Prop) -> A.
Axiom epsilon_spec :
forall (A:Type) (a:A), forall P, (exists x, P x) -> P (epsilon A a P).


Fixpoint power2 (n:nat) : nat :=
	match n with 
	| 0 => 1
	| S n => 2 * power2 n 
	end.

Eval compute in (power2 3).

Definition log2 (n:nat) : nat :=
	epsilon nat n (fun x => n=power2 x) .

Eval compute in (log2 8).

Definition epsilon_bool_subset (P : bool -> Prop) :
(exists x : bool, P x) -> { x : bool | P x }.
Admitted.


(***)

Inductive comparaison : Set :=
|Eq : comparaison
|Lt : comparaison
|Gt : comparaison.

Structure dec_order :=
{
	ord_car : Type;
	ord_rel : ord_car -> ord_car -> Prop;
	ord_compare : forall x y, ;
	ord_rel_compare : ord_car -> ord_car -> Prop;
	ord_irrefl : forall x, not (ord_rel x x)
}.

Eval ord_compare x y 