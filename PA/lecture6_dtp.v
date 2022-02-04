Require Import Utf8 List Program Arith Lia.
Import ListNotations.
Set Asymmetric Patterns.

(* Should not remain once you've completed all exercises. *)
Axiom todoimpl : forall {A}, A.
Ltac todo := apply todoimpl.

(** 
*** Correctness by construction

 Example: bounds checking.

 - Partial function *)

Definition nth_impossible : ∀ A, nat → list A → A.
Abort.

(** - A total version in Coq *)

Check nth : ∀ A, nat → list A → ∀ default : A, A.

(** - The total function, with types depending on values: *)

Example nth : ∀ A (l : list A), {n : nat | n < length l} → A.
Proof.
  induction l.
  - intros [n H]. simpl.
    exfalso. inversion H.
  - intros [ [| n'] H].
  + simpl in *. exact a.
  + apply IHl. exists n'. simpl in *. lia.
Defined.

Extraction nth.

(** - The computational content is mixed with the proof. *)


(** ** Subset types

 Subset types are Σ-types: 

  [{ x : A | P } <-> sigma A (fun x : A => P)]

 - Constructor: *)

Check (exist : forall A (P : A -> Prop),
          ∀ x : A, P x → { x : A | P x }).

(** - Projections:  *)

Check (proj1_sig : ∀ A P, {x : A | P x} → A).
Check (proj2_sig : ∀ A P (p : {x : A | P x}), P (proj1_sig p)).

(** - Binding notation: *)

Check (proj2_sig : forall A P (x : A | P x), P (proj1_sig x)).


(** 
*** Examples *)

Check (@exist nat (fun x : nat => x = x) 0 eq_refl
      : { x : nat | x = x }).

Check exist (fun x : nat => x = x) (S 0) eq_refl
      : { x : nat | x = x }.

Check exist (fun x : nat => x <= S x) (S 0) (le_S _ _ (le_n 1))
      : { x : nat | x <= S x }.

Check (fun x : { x : nat | x < 42 } => proj1_sig x)
  : { x : nat | x < 42 } -> nat.


(** 
*** Strong specifications

  *)

Definition euclid_spec :=
  forall (x : nat) (y : nat | 0 < y),
    { (q, r) : nat * nat | x = q * `y + r }.
    


(** *** Exercices *)

(** Notation [!] expresses an unreachable point of the program. *)

Program Definition imposs (H : 0 = 1) : False := !.

(** Choose your natural number wisely: *)

Program Definition exists_nonzero : { x : nat | x > 0 } := 3.
Print exists_nonzero.
(** If the specification is not inhabited then some obligations will remain unprovable. *)

Program Definition exists_lt_zero : { x : nat | x < 0 } := 0.
Admit Obligations.


Program Fixpoint safe_nth {A} (l: list A)
  (n:nat | n < length l) : A := 
  match l with 
  |nil => !
  |x :: xs => 
    match n with 
    |0 => x
    | S n => safe_nth xs n
    end
  end.
  
  (* Next Obligation.
  lia. 
  
  Print safe_nth. *)


(** *** Exercise
  Using a match expression and [!], implement a total [head] function: *)

Program Definition head {A}
        (l : { l : list A | l <> [] }) : A := 
        match l with
          | [] => !
          | a :: _ => a
        end.

(** Now look at its extraction to OCaml: *)

Eval cbv beta zeta delta [head] in head.
Extraction head.

(**
*** Program Example *)

Program Fixpoint euclid (x : nat)
        (y : nat | 0 < y) (* Binder for subsets *)
        { wf lt x } : (* Wellfounded definition *)
  { (q, r) : nat * nat | x = q * y + r } (* Rich type *) := 
    if lt_dec x y then (0,x)
    else 
      let 'pair q r := euclid (x-y) y in
      (S q, r)
  .


Admit Obligations.
Print euclid.

(** * Inductive Families
*)

Module Judgments.

(** 
 Judgments and in general inductively defined derivation trees can be
 represented using indexed inductive types. 

 A typical de Bruijn encoding of STLC. *)

Inductive type := 
  | cst | arrow : type -> type -> type.
Inductive term := 
  | var : nat -> term
  | lam : type -> term -> term
  | app : term -> term -> term.
Definition ctx := list type.

(** *** Judgments

  The typing relation can be defined as the inductive type: *)

Inductive typing : ctx -> term -> type -> Prop :=
| Var : forall (G : ctx) (x : nat) (A : type), 
    List.nth_error G x = Some A -> 
    typing G (var x) A

| Abs : forall (G : ctx) (t : term) (A B : type),
    typing (A :: G) t B ->
    typing G (lam A t) (arrow A B)

| App : forall (G : ctx) (t u : term) (A B : type),
    typing G t (arrow A B) ->
    typing G u A ->
    typing G (app t u) B.


(** ** Generalization by equalities

 Suppose you want to show:
*)

Lemma invert_var Γ x T (H : typing Γ (var x) T) :
  List.nth_error Γ x = Some T.
Proof. induction H as [G x' A Hnth|G t A B HB|G t u A B HAB HA].
(** [[
  x : nat
  G : ctx
  x' : nat
  A : type
  H : nth_error G x' = Some A
  ============================
   nth_error G x = Some A
subgoal 2 (ID 384) is:
 nth_error G x = Some (arrow A B)
subgoal 3 (ID 394) is:
 nth_error G x = Some B
]]
 *)
Abort.

Lemma invert_var Γ x T (H : typing Γ (var x) T) :
  List.nth_error Γ x = Some T.
Proof.
  inversion H. subst. assumption.
Qed.

End Judgments.

(** *** Eliminating Dependent Pattern-Matching 

  ** Indexed datatypes
    
  *** Vectors again *)

Inductive vect (A : Set) : nat -> Set :=
| vnil : vect A 0
| vcons (a : A) (n : nat) : vect A n -> vect A (S n).
(**
  - Indexed
  - Recursive
  - Terms _and_ types carry more information *)

Example v3 : vect bool 3 :=
 vcons _ true 2 (vcons _ true 1 (vcons _ false 0 (vnil _))).

Arguments vnil {A}. Arguments vcons {A} a {n} v.

Example v3' : vect bool 3 :=
 vcons true (vcons true (vcons false vnil)).

(**
*** Recall return clauses
*)

Fixpoint vmap {A B : Set} {n} (f : A → B) (v : vect A n) : vect B n
:= match v in vect _ k (* binds *) return vect B k with
   | vnil => vnil
   | vcons a n v' => vcons (f a) (vmap f v')
   end.

Definition vhead {A} {n} (v : vect A (S n)) : A :=
  match v in vect _ k
    return match k with 0 => unit | S k => A end with
    | vnil => tt
    | vcons a n v' => a
  end.
(**
  *** Exercise

  - Define two versions of [vtail], one using a hand-crafted
    return clause, and one in proof mode, using generalization with equalities.
  - Compare their Coq code and their extracted code.
 *)
Program Definition vtail {A} {n} (v : vect A (S n))
  : vect A n := todoimpl.

Definition vtail' {A} {n} (v : vect A (S n)) : vect A n.
Proof. todo. (* using tactics *) Defined.
Print vtail' .

Extraction vtail.
Extraction vtail'.

(**

  ** Relation to subset types}\begin{frame}{It's all the same}%

  - Inductive families vs subset types.
  - Structure vs property. *)

Definition ilist A n := {l : list A | length l = n}.


(** Let's show this type is _isomorphic_ to vectors. *)

Record Iso (A B : Type) :=
  { iso_lr : A -> B; iso_rl : B -> A;
    iso_lr_rl : forall x, iso_lr (iso_rl x) = x;
    iso_rl_lr : forall x, iso_rl (iso_lr x) = x }.

(** *** Exercise *)

Program Fixpoint vect_ilist {A n} (v : vect A n) : ilist A n :=
  todoimpl.

Fixpoint ilist_vect {A : Set} (l : list A) : vect A (length l) :=
  todoimpl.

Program Definition vect_ilist_iso {A} (n : nat) :
  Iso (vect A n) (@ilist A n) :=
  {| iso_lr := fun x => vect_ilist x ;
     iso_rl := fun x => ilist_vect x |}.
Solve Obligations with todo.

(** * Examples & Exercises
 
  ** More indexed types

 - Matrices, any bounded datastructure
*)

 Definition square_matrix {A} n := vect (vect A n) n.

(** - Balancing/shape invariants: e.g. red-black trees. *)

(** *** Examples *)

(**
 - Finite sets ([fin n] has [n] elements)

*)

Inductive fin : nat → Set :=
| fin0 n : fin (S n)
| finS n (f : fin n) : fin (S n).

Lemma fin_0_empty : fin 0 -> False.
Proof. intros f. inversion f. Qed.

(** Special inversion principle for [fin (S _)], for non-empty finite sets. *)

Definition fin_caseS (P : forall n, fin (S n) -> Type)
  (f0 : forall n, P n (fin0 n))
  (fS : forall n (f' : fin n), P _ (finS n f')) :
  forall n (f : fin (S n)), P n f.

refine (fun n f => match f as f' in fin n' return
         match n' return fin n' -> Type with
         | 0 => fun _ => True
         | S n => fun f' => P _ f' end f'
   with
   | fin0 n => f0 n
   | finS n f' => fS n f'
   end).
Defined.


(** *** Safe lookup with finite sets and vectors *)

Fixpoint lookup {A : Set} {n}
         (v : vect A n) (f : fin n) : A := todoimpl.

(** *** Definitional interpreters and well-typed syntax *)

 Inductive ty := nat_ty | arrow (t u : ty).
 Definition ctx := vect ty.

 Inductive expr {n} (Γ : ctx n) : ty → Set :=
 | var (f : fin n) : expr Γ (lookup Γ f)

 | app {tau tau'} 
       (f : expr Γ (arrow tau tau')) (u : expr Γ tau) 
   : expr Γ tau'

 | lam {tau tau'}
       (t : @expr (S n) (vcons tau Γ) tau') 
   : expr Γ (arrow tau tau').

 (** - No ill-typed terms, by construction. *)

Example nat_id := lam vnil (tau:=nat_ty) (var _ (fin0 0)).
(** *** And definitional interpreters *)

Fixpoint interp_type (ty : ty) : Set :=
 match ty with
   | nat_ty => nat
   | arrow tau tau' => interp_type tau → interp_type tau'
 end.

(** This will typecheck only once you define lookup: it requires its computational behavior. *)

(* Check nat_id : expr vnil (arrow nat_ty nat_ty) *)

Example nat_id_type : interp_type (arrow nat_ty (lookup (vcons nat_ty vnil) (fin0 0))) = (nat -> nat) :=
  todoimpl. (** needs to solve lookup exercise to use [eq_refl] here *)

(** *** Interpretation: valuations *)

Definition valuation {n} (Γ : ctx n) :=
  ∀ f : fin n, interp_type (lookup Γ f).

Definition empty_val : valuation vnil.
Proof. intros f. refine (match f with end). Defined.

Definition extend_val {n} {Γ : ctx n} {t} (x : interp_type t)
           (val : valuation Γ) : valuation (vcons t Γ).
Proof. unfold valuation. intros f. revert n f Γ val.
  refine (fin_caseS _ _ _); todo.
Defined.

(** *** Interpretation *)

Fixpoint interp {n} {Γ : ctx n} {ty : ty} (v : valuation Γ)
         (x : expr Γ ty) : interp_type ty :=
  match x with
  | var f => v f
  | app tau tau' f u => (interp v f) (interp v u)
  | lam tau tau' b =>
    fun x : interp_type tau => interp (extend_val x v) b
  end.

Example interp_nat_id := interp empty_val nat_id.
Eval compute in interp_nat_id. (** Exercise check result *)
(* Should reduce to:
[[
= λ x : nat, x
  : interp_type (arrow nat_ty (lookup (vcons nat_ty vnil) (fin0 0)))
]] *)