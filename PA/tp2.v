Axiom todo : forall {A}, A.

(* 2.1 Equality *)

Definition sym (A:Type) (x y:A) (e:x=y) : y = x := 
	eq_ind x (fun y0 => y0=x) eq_refl y e.

		
Definition trans (A:Type) (x y z:A) (e1:x=y) (e2:y=z) : x=z := 		
	eq_ind y (fun z0 => x=z0) e1 z e2 .

Definition congr (A B:Type) (f:A->B) (x y:A) (e:x=y) : f x = f y := 
	eq_ind x (fun y0 => f x = f y0) eq_refl y e.

Print eq_rect.



Lemma dcongr (A:Type) (B:A->Type) (f:forall x:A, B x) (x y:A) (e:x=y) :
  eq_rect x B (f x) y e = f y.
Proof.
case e.
unfold eq_rect.
reflexivity.
Qed.

(* 3 Universes *)

(* 4.1 *)

Check (forall (P:Prop),P).
Check (forall (P:Type),P).
Check (forall (PP:Prop->Prop), exists (P:Prop), PP P).
Fail Check (forall (PP:Type->Type), exists (P:Type), PP P).

Definition conj (A B:Prop) : Prop :=
  forall Q:Prop, (A->B->Q) -> Q.

Definition conj_i (A B: Prop) (a:A) (b:B) : conj A B := 
	fun Q (f:A->B->Q) => f a b.

Definition conj_e1 (A B:Prop) (p: conj A B) : A := 
	p A (fun A B => A).

Definition conj_e2 (A B:Prop) (p: conj A B) : B := 
	p B (fun A B => B).

Definition disj (A B:Prop) : Prop := 
	forall Q:Prop, (A->Q) -> (B->Q) -> Q.

Definition disj_i1 (A B:Prop) (a:A) : disj A B := 
	fun Q f f' => f a.

Definition disj_i2 (A B:Prop) (b:B) : disj A B := 
	fun Q f f' => f' b.
	
Definition disj_e (A B:Prop) (p: disj A B) (Q:Prop) (f:A->Q) (f':B->Q) : Q := 
	p Q f f'.

Definition ex (A:Type) (P: A -> Prop) : Type := 
	forall Q:Prop, (forall x:A, P x -> Q) -> Q.

Definition ex_i (A :Type) (P: A -> Prop) (a:A) (b:P a) : ex A P  :=
	fun Q (f:forall x:A, P x -> Q) => f a b.

Definition ex_e (A:Type) (P:A->Prop) (p: ex A P) (Q:Prop) (f:forall (a:A) (b:P a), Q) : Q := 
	 p Q f.

Definition equ (A:Type) (a b:A) : Type := 
	forall (P:A->Prop), P a -> P b.

Definition equ_refl (A:Type) (x:A) : equ A x x  :=
	fun P h => h
	.

Definition equ_ind : todo := todo.

Definition equ_sym : todo := todo.
Definition equ_trans : todo := todo.

Definition equ_congr : todo := todo.

(* 4.2 *)

Definition bool : Prop :=
  forall Q:Prop, Q->Q->Q.

Definition true : bool := todo.
Definition false : bool := todo.

Definition ifthenelse : todo := todo.

Definition band : todo := todo.
Lemma band_ff : todo.
Proof. apply todo. Qed.
Lemma band_ft : todo.
Proof. apply todo. Qed.
Lemma band_tf : todo.
Proof. apply todo. Qed.
Lemma band_tt : todo.
Proof. apply todo. Qed.

(* 4.3 *)

Definition nat : Prop :=
  forall Q:Prop, Q -> (Q->Q) -> Q.

Definition zero : nat := todo.

Definition succ (n:nat) : nat := todo.

(* iterate n times successor on m *)
Definition plus (n m:nat) : nat := todo.

Definition mult (n m:nat) : nat := todo.

Eval compute in (mult (succ (succ zero)) (succ (succ (succ zero)))).

(* 5. *)

Definition pnat : Type := todo.

Definition pzero : pnat := todo.

Definition psucc (n:pnat) : pnat := todo.