Require Import Bool Arith List.
Import ListNotations.

Definition cons [A:Type] (e :  A) (l: list A) := 
	e :: l
.

Definition decons [A:Type] (l: list A) := 
	match l with 
	| [] => None
	| h::t => Some (h,t)
	end.

Fixpoint nth [A:Type] (l: list A) n := 
match n,l with 
| _,[] => None
| 0,h::_ => Some h
| S n, _::t => nth t n 

end.

Compute nth [1;2;3] 2. 
Compute nth [1;2;3] 4.

Inductive tree (A:Type) : Type := 
|leaf : A -> tree A
|node : tree A -> tree A -> tree A 
.

Arguments leaf {A}.
Arguments node {A}.


Definition blist (A:Type) : Type := 
list (nat * tree A)
.

Check  [ (0,leaf 0)] : blist nat.
Check  [] : blist nat.

Fixpoint tsize {A} (t: tree A) := 
match t with 
|leaf _ => 1
|node t _ => 2 * (tsize t) 
end.

Compute tsize (node (leaf 0) (leaf 0)).
Compute tsize (node (node (leaf 0) (leaf 1)) (node (leaf 1) (leaf 0))).

Fixpoint tcons {A} (t:tree A) (l:blist A) := 
	match l with 
	|[] => [(tsize t, t)]
	|(st',t')::ll =>  
		let st  := tsize t in
		if st =? st' 
		then tcons (node t t') ll 
		else (st,t)::l
end.

Definition bcons {A} (a:A) l := tcons (leaf a) l.

Compute bcons 1 (bcons 2 (bcons 3 (bcons 4 []))).
Compute bcons 1 (bcons 2 (bcons 3  [])).

Fixpoint tdecons {A} (st:nat) (t:tree A) (l:blist A) := 
	match t with
	|leaf a =>  (a,l)
	|node fg fd => 
		let size := st-1 in
		tdecons size fg ((size,fd)::l) 
	end.


Definition l := bcons 1 (bcons 2 (bcons 3  [])).

Definition bdecons [A:Type] (l: blist A) := 
	match l with 
	| [] => None
	| (st,t)::ll => Some (tdecons st t ll)
	end.

Compute bdecons l .


Fixpoint tnth [A:Type] (t: tree A) n size := 
	match t,n with 
	|leaf a,0 => Some a 
	|leaf _,_ => None 
	|node fg fd, _ => 
		let size' := size/2 in 	
		if n <? size'  
		then tnth fg n size' 
		else tnth fd (n-size') size'
	end.	
	

Fixpoint bnth [A:Type] (l: blist A) n := 
match l with 
	| [] => None
	| (st,t)::ll => 
		if n <? st 
		then tnth t n st
		else bnth ll (n-st) 
end.

Compute l.
Compute bnth l 1.

Fixpoint list_to_blist [A] (l:list A) : blist A := 
	match l with 
	|[] => []
	|h::t => bcons h (list_to_blist t)
end.

Definition l' := list_to_blist [1;2;3;4;5;6;7;8].
Compute bnth l' 4.


