Require Import Bool Arith List.
Import ListNotations.

Module dep_typ.

Inductive fulltree (A:Type) : nat -> Type := 
|leaf : A -> fulltree A 0
|node n : fulltree A n -> fulltree A n -> fulltree A (S(n)) 
.

Arguments leaf {A}.
Arguments node {A}.

Definition blist (A:Type) : Type := 
list {n & fulltree A n}
.

Definition tcast {A} {n} {m} (v: fulltree A n)(h : n = m) : fulltree A m :=
  match h with
  | eq_refl => v
  end.

Fixpoint tcons {A} {n:nat} (t:fulltree A n) (l:blist A) := 
	match l with 
	|[] => [existT _ n t]
	|(existT _ n' t')::ll =>
		match Nat.eq_dec n n' with
		|left p =>  tcons   (node _ (tcast t p) t')   ll 
		|right _=> (existT _ n t) ::l
		end
end.


Definition bcons {A} (a:A) l := tcons (leaf a) l.
Compute bcons 1 (bcons 2 (bcons 3 (bcons 4 []))).
Compute bcons 1 (bcons 2 (bcons 3  [])).

Fixpoint tdecons {A} {n} (t:fulltree A n) (l:blist A) := 
	match t with
	|leaf a => (a,l)
	|node n fg fd => 
		tdecons fg ((existT _ _ fd)::l) 
	end.

Definition bdecons [A:Type] (l: blist A) := 
	match l with 
	| [] => None
	| (existT _ _ t)::ll => Some (tdecons t ll)
	end.

Definition l := bcons 1 (bcons 2 (bcons 3  [])).
Compute l .
Compute bdecons l .

Fixpoint tnth [A:Type] {st} (t: fulltree A st) n := 
	match t,n with 
	|leaf a,0 => Some a 
	|leaf _,_ => None 
	|node st fg fd, _ => 
		let st' := 2^(pred st) in
		if n <? st'  
		then tnth fg n
		else tnth fd (n-st')
	end.	
	

Fixpoint bnth [A:Type] (l: blist A) n := 
match l with 
	| [] => None
	| (existT _ st t)::ll => 
		let st' := 2^st in
		if n <? st' 
		then tnth t n
		else bnth ll (n-st') 
end.

Compute l.
Compute bnth l 1.

End dep_typ.

Inductive tree (A:Type) : Type := 
|leaf : A -> tree A 
|node : tree A -> tree A -> tree A
.

Arguments leaf {A}.
Arguments node {A}.


Definition option_bind {A B} (o : option A) (f:A -> option B) : option B :=
 match o with
 | Some x => f x
 | None => None
 end.

Infix ">>=" := option_bind (at level 20, left associativity).

Fixpoint perfect_depth {A} (t: tree A) : option nat := 
match t with 
|leaf _ => Some 0
|node fg fd => 
	perfect_depth fg >>= fun size_fg => 
	perfect_depth fd >>= fun size_fd =>
	if size_fg =? size_fd then Some (S(size_fd+size_fd))
	else None
end.

Definition t1 := (node (leaf 0) (leaf 0)).
Definition t2 := (node t1 (leaf 0)).
Compute perfect_depth t1.
Compute perfect_depth t2.

Module Type MONAD.
  Parameter t : Type -> Type.
  Parameter bind : forall {A B}, t A -> (A -> t B) -> t B.
  Parameter ret : forall {A}, A -> t A. (* ret, since return is a Coq keyword *)
End MONAD.

Check List.filter_map.

Require Import Bool Arith List.
Module MList <: MONAD.
  Definition t := list.
  Definition ret  (a:nat) := [a].
  Definition bind  (l:list nat) (f:nat->list nat) := List.filter_map Nat.eqb f l.
End MList.

Infix ">>=" := MList.bind (at level 20, left associativity).

Definition scoring (n:nat) := [n+3;n+5;n+7].

Fixpoint next_scores l n := 
	match n with 
	|0 => l
	|S n' => 
		next_scores l n' >>= scoring
	end.

Compute next_scores [0] 2.

Check List.flat_map.