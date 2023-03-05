Require Import PolyDefs PolyVal Bool.
Import ZArith Lia.
Require Import PolyArith Valid.


(* Boolean Formulas *)
 
Definition impb (b1 b2: bool) := if b1 then b2 else true.
Definition cst_poly (z:Z) := {| VP_value := (Cst z); VP_prop := eq_refl |}.

Inductive form : Set :=
| f_true 	: form 
| f_false   : form 
| f_var 	: nat -> form 
| f_and 	: form -> form -> form 
| f_or  	: form -> form -> form
| f_not 	: form -> form
| f_imp 	: form -> form -> form
.

Fixpoint eval_form (f:form) (val : nat -> bool) : bool := 
  match f with 
  | f_true => true
  | f_false => false
  | f_var i => val i
  | f_and f1 f2 => eval_form f1 val && eval_form f2 val
  | f_or f1 f2 => eval_form f1 val || eval_form f2 val
  | f_not f1 => negb (eval_form f1 val	)
  | f_imp f1 f2 => impb (eval_form f1 val) (eval_form f2 val)
  end
.  

#[local] Hint Constructors form : core.
Notation "A ∧ B" := (f_and A B) (at level 30, right associativity).
Notation "A ∨ B" := (f_or A B) (at level 35, right associativity).
Notation "A → B" := (f_imp A B) (at level 49, right associativity, B at level 50).
Notation "⊤" := (f_true) (at level 5).
Notation "⊥" := (f_false) (at level 5).
Notation "# x" := (f_var x) (at level 10).
Notation "! A" := (f_not A) (at level 11).


Definition valuation := (fun x => match x with |0 => false |_=> true end).

Eval compute in (eval_form (# 0 ∨ # 1) valuation).
(* Eval compute in (eval_form (# 0 → # 1) valuation).
Eval compute in (eval_form (# 1 → # 0) valuation).
Eval compute in (eval_form (# 1 → # 1) valuation). *)


From Coq Require Import List .
Import ListNotations .

Ltac list_add a l :=
  let rec aux a l n :=
    match l with
    | [] => constr :(( n , a :: l ))
    | a :: _ => constr :(( n , l ))
    | ?x :: ?l =>
      match aux a l ( S n ) with
      | (?n , ?l ) => constr :(( n , x :: l ))
      end
    end 
  in
  aux a l O 
.

Ltac read_term_ f l :=
match f with
|negb ?x => 
  match read_term_ x l with
  |(?x' , ?l') => constr:(( f_not x' , l'))
  end
|andb ?x ?y =>
  match read_term_ x l with
  |(?x' , ?l') => match read_term_ y l' with
    |(?y' , ?l'') => constr:(( f_and x' y' , l''))
  end end
|orb ?x ?y =>
  match read_term_ x l with
  |(?x' , ?l') => match read_term_ y l' with
    |(?y' , ?l'') => constr:(( f_or x' y' , l''))
  end end
|impb ?x ?y => 
  match read_term_ x l with
  |(?x' , ?l') => match read_term_ y l' with
    |(?y' , ?l'') => constr:(( f_imp x' y' , l''))
  end end
|false => constr:((f_false , l))
|true => constr:((f_true , l))

|_ => 
  match list_add f l with
  | (?n , ?l') =>  constr:(( f_var n , l'))
  end
end.


Ltac read_term f := read_term_ f (@nil bool).

Goal forall b : bool , True .
intros b.
let v := read_term (andb b ( negb b)) in
idtac v.
let v := read_term (orb b (negb ( negb b))) in
idtac v.
let v := read_term (andb b (negb false)) in
idtac v.
let v := read_term (orb (negb false) true) in
idtac v.
let v := read_term (impb (negb b) true) in
idtac v.
let v := read_term (impb (false) true) in
idtac v.
Abort.


Definition sub_poly (p q:valid_poly) := sum_poly p (mul_poly (cst_poly (-1)%Z) q).

Lemma poly_val_cst (z:Z) (val:nat->Z) : (poly_val (cst_poly z) val) = z.
Proof.
  unfold poly_val. unfold cst_poly.
  simpl.
  reflexivity.
Qed.

Lemma poly_val_sub (p q : valid_poly) (val:nat->Z) : 
poly_val (sub_poly p q) val = Z.sub (poly_val p val)  (poly_val q val) 
.
Proof.
  unfold sub_poly.
  rewrite sum_poly_val.
  rewrite mul_poly_val.
  simpl.
  destruct (poly_val q val); intuition.
Qed.


Fixpoint to_poly (f:form) (val:nat->bool) : valid_poly := 
  match f with 
  |f_true => cst_poly 1%Z
  |f_false => cst_poly 0%Z
  |f_and a b => mul_poly (to_poly a val) (to_poly b val)
  |f_or a b => sub_poly (sum_poly (to_poly a val) (to_poly b val)) (mul_poly (to_poly a val) (to_poly b val))
  |f_not a =>  sub_poly (cst_poly 1%Z) (to_poly a val)
  |f_var n => if (val n) then cst_poly 1%Z else cst_poly 0%Z 
|f_imp a b => sub_poly (sum_poly (sub_poly (cst_poly 1%Z) (to_poly a val)) (to_poly b val)) (mul_poly (sub_poly (cst_poly 1%Z) (to_poly a val)) (to_poly b val))
end.

Definition z_of_bool := (fun x : bool => if x then 1%Z else 0%Z).

Theorem eval_form_to_poly  (f:form) (val : nat -> bool) : 
z_of_bool (eval_form f val) = 
poly_val (to_poly f val) (fun n => z_of_bool (val n)).
Proof.
  induction f; simpl eval_form; simpl to_poly.
  - reflexivity.
  - reflexivity.
  - destruct (val n); reflexivity.
  - rewrite mul_poly_val.
    rewrite <- IHf1. rewrite <- IHf2.
    destruct (eval_form f1 val).
    + rewrite andb_true_l. simpl z_of_bool. lia. 
    + rewrite andb_false_l. simpl z_of_bool. lia.
  - rewrite poly_val_sub. rewrite sum_poly_val. rewrite mul_poly_val. 
    rewrite <- IHf1. rewrite <- IHf2.
    destruct ((eval_form f1 val)); simpl z_of_bool.
    + destruct (eval_form f2 val); simpl; reflexivity.
    + simpl. lia.
  - rewrite poly_val_sub.
    rewrite poly_val_cst. 
    rewrite <- IHf.  
    destruct (eval_form f val); simpl; reflexivity.
  - rewrite poly_val_sub. rewrite sum_poly_val.
    rewrite mul_poly_val. rewrite poly_val_sub.
    rewrite <- IHf1. rewrite <- IHf2.
    rewrite poly_val_cst. 
    destruct (eval_form f1 val); simpl impb; simpl z_of_bool; lia.
Qed.

Definition eq_form (f1:form) (l1: list bool) (f2:form) (l2: list bool) :=
  forall (val:nat->Z), 
  poly_val (to_poly f1 (fun n => List.nth n l1 false)) val = poly_val (to_poly f2 (fun n => List.nth n l1 false)) val 
  .

Eval compute in (VP_value (to_poly (f_and f_true f_false) (fun n => false))).


(* Example : here we can prove that (false || b) = false, in the environnement where b is true *)
Goal (eq_form (f_and f_false (f_var 0)) [true] f_false [] ).
unfold eq_form. 
simpl.
unfold cst_poly.
intro.
rewrite mul_poly_val.
unfold poly_val.
simpl.
reflexivity.
Qed.

(* Example : here we can prove that (b0 || b1) = (b1 || b0), when b0 is true and b1 is false (in both environnements) *)
Goal (eq_form (f_and (f_var 0) (f_var 1)) [true; false] (f_and (f_var 1) (f_var 0)) [true; false] ).
unfold eq_form. 
simpl.
unfold cst_poly.
intro.
rewrite mul_poly_val.
rewrite mul_poly_val.
unfold poly_val.
simpl.
reflexivity.
Qed.

(* Example : here we can prove that ((b0 || b1) && b2) = (b2 && (b1 || b0)), when b0 is true and b1 is false (in both environnements) *)
Goal (eq_form  (((# 0) ∨ (# 1)) ∧ # 2) [true; false; false] (# 2 ∧ ((# 1) ∨ (# 0))) [true; false; false] ).
unfold eq_form. 
simpl.
unfold cst_poly.
intro.
rewrite mul_poly_val.
rewrite mul_poly_val.
unfold sub_poly.
unfold cst_poly.
rewrite sum_poly_val.
rewrite sum_poly_val.
rewrite sum_poly_val.
rewrite sum_poly_val.
simpl.
reflexivity.
Qed.