Require Import Bool Arith List.
Import ListNotations.

Fixpoint length [A:Type] (l:list A) := 
match l with 
|[] => 0
|_::t => S (length t)
end.

Compute (length [0;1;2;3]).
Compute (length []).

Definition l1 := [0;1;2;3].
Definition l2 := [0;1] .

Fixpoint concat [A:Type] (l1:list A) (l2:list A) := 
match l1 with 
|[] => l2
|h::t => h::(concat t l2)
end.


Compute (concat l1 l2).
Compute (concat [] l2).
Compute (concat l1 []).
Compute (concat [] []).


(* Fixpoint rev [A:Type] acc (l:list A)  := 
match l with 
|[] => acc
|h::t => rev (h::acc) t
end. *)

Definition rev [A:Type] (l:list A)  := 
let rev_ := 
  fix rev_ (acc: list A) (l:list A) :=
  match l with 
  |[] => acc
  |h::t => rev_ (h::acc) t
  end
in
rev_ [] l.

Compute (rev l1).

Fixpoint map [A B : Type] (f: A->B) (l:list A) : list B :=
  match l with 
  |[] => []
  |h::t => (f h)::(map f t)
  end.

Compute (map (fun n => S n) l1).
Compute (map (fun n => S n) l2).

Fixpoint filter [A:Type] (p:A->bool) (l:list A) :=
  match l with
  |[] => []
  |h::t => if (p h) then h::(filter p t) else (filter p t)
  end.

Compute (filter (fun n => 0 <? n) l1).
Compute (filter (fun n => 0 <? n) l2).
Compute (filter (fun n => 0 <? n) (rev l1)).

Fixpoint fold_left [A B:Type] (f: A->B->A) acc l := 
  match l with 
  |[] => acc
  |h::t => fold_left f (f acc h) t
  end.

Definition list_sum := 
  fold_left (fun acc h => acc+h ) 0.

Compute (list_sum l1).
Compute (list_sum l2).

Definition seq a n := 
  match n with 
  |0 => []
  |S n' => a :: (seq (S a) n')
  end.
  
Compute (seq 0 3). 
Compute (seq 3 5).

Definition head [A:Type] (l : list A) := 
match l with 
|[] => None 
|h::_ => Some h
end.

Compute (head []). 
Compute (head l1).

Fixpoint last [A:Type] (l : list A) := 
match l with 
|[] => None 
|[x] => Some x 
|_::t => last t
end.

Compute (last []). 
Compute (last l1).

Fixpoint nth [A:Type] (l : list A) n := 
match l,n with 
|[],_ => None  
|h::_, 0 => Some h
|_::t, S n' => nth t n' 
end.

Compute (nth [] 2). 
Compute (nth l1 2).

Definition forallb [A:Type] p (l:list A) :=
  fold_left (fun acc h => acc && (p h )) true l  
.

Compute (forallb (fun n => 0 <? n) l1).
Compute (forallb (fun n => 0 <? n) (seq 1 5)).

Fixpoint increasing (l :list nat) :=
  match l with
  |[] => true
  |[x] => true
  |h::((h2::_) as t) => (h <? h2) && (increasing t)
  end.

Compute (increasing (seq 1 5)).
Compute (increasing (rev l1)).
Compute (increasing [1;1]).

(* Definition add n m := nat_rect _ m (fun _ => S) n.
Compute add 2 3. *)


Fixpoint delta (l :list nat) n :=
  match l with
  |[] |[_] => true
  |h::((h2::_) as t) => 
    if (h+n <=? h2) then (delta t n) else false 
  end.

Compute (delta l1 2) .
Compute (delta l1 1) .
Compute (delta [1;3;6;8] 2) .
Compute (delta [1;3;6;8] 3) .

Fixpoint split_at [A:Type] (l:list A) n :=
  match l,n with
  |[],_ => ([],[])
  |_,0 => ([], l)
  |h::t,S n' =>
    let '(l1,l2) := (split_at t n') in
    ((h::l1),l2)
  end
.

Definition split [A:Type] (l:list A) := 
  split_at l ((length l)/2).


Compute split l1.
Compute split (seq 0 3).
Compute split (seq 0 0).

(* Fixpoint merge l1 l2 := 
  match l1,l2 with 
  |[],_ => l2
  |_,[] => l1
  |h::t,h2::t2 => 
    if h <? h2 
    then h::(merge t (h2::t2))
    else h2::(merge (h::t) t2)
  end. *)


Fixpoint merge l1 l2 := 
  match l1 with 
  |[] => l2
  |h::t => 
    (fix merge_ l2 := 
      match l2 with 
      |[] => l1  
      |h2::t2 => 
        if h <? h2 
        then h::(merge t l2)
        else h2::(merge_ t2)
      end) l2
  end.

Compute merge [1;2;6] [0;2;3].
Compute merge [1;2;6] [1;2;3;7].
Compute merge [1;4;6] [0;2;3;7].

Fixpoint mergesort (n:nat) (l: list nat) :=
  match l,n with
  |[],_ |[_],_ |_,0 => l
  |_,S n => 
    let '(l1,l2) := split l in 
    let l1 := (mergesort (n) l1) in 
    let l2 := (mergesort (n) l2) in 
    merge l1 l2
  end. 

Compute mergesort 1000 [4;3;8].
Compute mergesort 1000 (rev (seq 0 18)).

Fixpoint powerset [A:Type] (l:list A) :=
  match l with 
  |[] => [[]]
  |h::t => 
    let power := (powerset t ) in 
    power++(map (fun x => h::x) power)
  end.

Compute powerset [0;1;2]. 
