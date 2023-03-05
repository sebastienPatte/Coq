Definition sym (A:Type) (x y :A) (p:x=y) : y = x := 
	eq_ind x (fun y0 => y0=x) eq_refl y p.

Definition trans (A:Type) (x y z:A) (p1:x=y) (p2:y=z) : x = z := 
	eq_ind y (fun x0 => x=x0) p1 z p2.
	
Definition cong (A B:Type) (f:A->B) (x y:A) (p:x=y) : f x = f y := 
	eq_ind x (fun x0 => f x = f x0) eq_refl y p.

Definition P := Prop.
Definition T := Type.

Check (forall p:P, p ) : P.
Fail Check (forall p:T, p ) : T.


