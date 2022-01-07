
Definition id : forall X:Prop, X->X := 
	fun (X:Prop) (a:X) => a.
Check id (True->True) : (True->True)->True->True. 

(*forall (A:Type)(x y:A), x=y -> y=x*)

(* 2 *)

Definition sym : forall (A:Type)(x y:A), x=y -> y=x :=
	fun (A:Type) (x y:A) (H: x = y) => 
		eq_ind x (fun z:A => z=x)
		(eq_refl x) y H.

Definition trans : forall (A:Type)(x y z:A), x=y -> y=z -> x=z := 
	fun (A:Type) (x y z : A) (H1 : x=y) (H2:y=z) =>
		eq_ind y (fun y0:A => x=y0)
		H1 z H2.


Definition cong : forall (A B:Type) (f:A->B) (x y:A), x=y -> f x = f y := 
	fun (A B:Type) (f:A->B) (x y:A) (H:x=y) =>
		eq_ind x (fun t:A => f x=f t) 
		(eq_refl (f x)) y H
	.

(*Lemma cong_dep : 
	forall (A:Type) (B:A->Type) (f:forall x:A, B x) (x y:A),
		x=y -> f x= f y.*)

(* 3 *)

Definition t := Prop.
Check (forall (x:t), x):t.

Definition u := Type.
Fail Check (forall (x:u), x):u.
Check (forall (P:Type), P):Type.


(* 4 *)

Definition imp_and (A:Prop)(B:Prop) := 
	forall X : Prop,  (A -> B -> X ) -> X.





