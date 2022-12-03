Lemma s : 3*3=9.
Proof.
	apply eq_refl.
Qed.
(* (a) *)
Inductive aexpr (N:Type)  := 
| cst : N -> aexpr N
| var : nat -> aexpr N
| add : aexpr N -> aexpr N -> aexpr N
.
(* (b) *)
Check (cst).

(* (c) *)
Print aexpr_ind.

Fixpoint aexpr_iter (N : Type) (P : Type)
           (Pcst : N -> P)
           (Pvar : nat -> P)
           (Padd : aexpr N -> P -> aexpr N -> P -> P)
           (e : aexpr N) : P :=
  match e with
    | cst _ n => Pcst n
    | var _ n => Pvar n
    | add _ x y => Padd x (aexpr_iter N P Pcst Pvar Padd x)
                      y (aexpr_iter N P Pcst Pvar Padd y)
  end.

Inductive iff (A B:Prop) : Prop :=
|iff_intro : (A -> B) -> (B -> A) -> iff A B
.

Definition iff_rd := 
fun (A B:Prop) (P: iff A B -> Type) 
 (f: forall (a : A -> B) (b : B -> A), P(iff_intro A B a b))
 (i: iff A B) => 
 match i  with 
 | iff_intro _ _ x x0 => f x x0
 end
 
.

Print iff_ind.
Print aexpr_rect.

Definition iff_l (A B:Prop) (e: iff A B) :=  
  iff_rd A B (fun _ => A -> B) (fun l _ => l) e.

  Definition iff_out (A B : Prop) (e : iff A B) : A -> B :=
  iff_ind A B (A -> B) (fun l _ => l) e.
Parameter (A B:Prop).
Check (iff_out B  (iff A B )).
Check (iff_l B  (iff A B )).