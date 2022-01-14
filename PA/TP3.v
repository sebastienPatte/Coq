Inductive bool : Type := true : bool | false : bool.


Definition negb (b:bool) :=
match b with 
|true => false 
|false => true   
end.

Definition andb (b1:bool) (b2:bool) :=
match b1,b2 with 
|true,true => true 
|_,_ => false
end.

Eval compute in (fun x:bool => negb (andb false x)).

Eval compute in (fun x:bool => negb (andb x false)).

Parameter T1 T2 : Type.
Parameter t1:T1.
Parameter t2:T2.

Definition g (b:bool) := 
match b return if b then T1 else T2 with 
| true => t1 
| false => t2 end.

Definition g2 (b:bool) := 
match negb b as b2 return if b2 then T2 else T1 with 
| true => t2 
| false => t1 end.

Locate and.

Inductive even : nat -> Prop :=
| even0 : even 0
| evenS n : even n -> even (S (S n)).


Lemma even_is_double : forall n, even n -> exists m, n=m+m.
Proof.
	induction 1.
	exists 0.
	reflexivity.
	destruct IHeven as (m, H0).
	exists (S m).
	rewrite H0.
	unfold plus.
	auto.
Qed.
	

Lemma even_is_double' n : 
(even n -> exists m, n=m+m) /\
(even (S n) -> exists m, S n=m+m).
Proof.
	
 	induction n; simpl;split;intros.
	split.
	intros.
	exists 0.
	
	reflexivity.
	intro.
	inversion H.
	
	destruct IHn.
	split.
	destruct H0.
	inversion_clear H.
	
	
	
	
	
	



