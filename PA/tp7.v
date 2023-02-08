(* Functional and dependently typed programming *)

Axiom todo : forall {A}, A.

(* Let's have a look at vectors again. *)

Inductive vec (A : Type) : nat -> Type :=
| vnil : vec A 0
| vcons (a : A) (n : nat) (v : vec A n) : vec A (S n).

Arguments vnil {_}.
Arguments vcons {_} _ {_}.

(* You can write the head and tail functions without needing a default case. *)
(* Let's think about how we would do it on paper first. *)

Definition head {A n} (v : vec A (S n)) : A :=
  match v with 
  |vcons a n0 => a
  end.

  Print IDProp.
  Print idProp.
  Print head.

Definition tail {A n} (v : vec A (S n)) : vec A n :=
  match v with 
  |vcons a t => t
  end.

(* Coq is not always smart enough to see that some patterns are impossible.
  Consider the following zip function. How can you actually define it?
*)

Fail Fixpoint zip {A B n} (v : vec A n) (v' : vec B n) : vec (A * B) n :=
  match v, v' with
  | vnil, vnil => vnil
  | vcons a v, vcons b v' => vcons (a, b) (zip v v')
  end.

Fixpoint zip' {A B n} (v : vec A n) (v' : vec B n) : vec (A * B) n :=
  match v as w in vec _ m
  return 
    vec B m -> vec (A * B) m
  with
  | vnil => fun v' => vnil   
  | vcons a v => fun v' => vcons (a,head v') (zip' v (tail v')) 
    end v' 
  .

(* Are you satisfied when comparing to the ideal zip above? *)

(* Equations lets us deal with dependent pattern matching nicely. *)

From Equations Require Import Equations.

Equations zip {A B n} (v : vec A n) (v' : vec B n) : vec (A * B) n :=
  zip vnil vnil := vnil ;
  zip (vcons a v) (vcons b v') := vcons (a, b) (zip v v').


(* We can also define a function for accessing elements. *)
(* We can use bounded natural numbers to do it. *)

Inductive fin : nat -> Type :=
| fin0 n : fin (S n)
| finS n (x : fin n) : fin (S n).

Arguments fin0 {n}.
Arguments finS {n}.

Equations vnth {A n} (v : vec A n) (x : fin n) : A :=
  vnth (vcons a v) (fin0) := a;
  vnth (vcons _ v') (finS x) := vnth v' x.

(* We can now prove that zip and vnth commute. *)

(* To prove it without using too much Equations facilities we can prove first
  the following lemma.
*)

Lemma vec_expand :
  forall A n (v : vec A (S n)),
    v = vcons (head v) (tail v).
Proof.
  intros.
  refine match v with |vcons a v' => _ end.
  reflexivity.
Qed.

(* We will need simp from Equations because by default Equations definitions are opaque.
  simp vnth for instance will apply simplications of the vnth function.
*)

Lemma zip_vnth_by_hand :
  forall A B n (v : vec A n) (v' : vec B n) (x : fin n),
    vnth (zip v v') x = (vnth v x, vnth v' x).
Proof.
  intros.
  induction x.
  - erewrite vec_expand with (v:= v).
    erewrite vec_expand with (v:= v').
    simp zip vnth.
    reflexivity.
  - erewrite vec_expand with (v:= v).
    erewrite vec_expand with (v:= v').
    simp zip vnth.
Qed.

(* Using dependent elimination we don't need the extra lemma.
  It works a bit like destruct but instead of giving names for the variables
  you give patterns directly. For lists you would have for instance
  dependent elimination l as [ nil | x :: r ].
  This uses Equations's machinery so you can actually remove inaccessible
  patterns like we did for zip or vnth.
*)

Lemma zip_vnth_without_funelim :
  forall A B n (v : vec A n) (v' : vec B n) (x : fin n),
    vnth (zip v v') x = (vnth v x, vnth v' x).
Proof.
  intros.
  induction x.
  - dependent elimination v.
    dependent elimination v'.
    simp zip vnth.
    reflexivity.
  - dependent elimination v.
    dependent elimination v'.
    simp zip vnth.
Qed.

(* We can also use the funelim tactic to do the case disjunction for us. *)

Derive Signature NoConfusion NoConfusionHom for fin.
Derive NoConfusion for vec.

Lemma zip_vnth :
  forall A B n (v : vec A n) (v' : vec B n) (x : fin n),
    vnth (zip v v') x = (vnth v x, vnth v' x).
Proof.
  intros A B n v v' x.
  funelim (vnth v x). (* Notice how both v and x are destructed at once. *)
  - funelim (vnth v' _).
    simp zip vnth. reflexivity.
  - funelim (vnth v'0 _).
    simp zip vnth.
  (* Well, this only works if you have defined vnth properly. *)
Qed.

(* How does this work? *)
Search zip. (* You will see many properties that were automatically proven. *)
(* They are used by simp and funelim. *)
(* For instance we could use zip_equation_2 to rewrite by hand. *)

(* These equations can also be found in the graph. *)
Print zip_graph.
Check zip_graph_correct.

(* We can also use notations within Equations definitions *)

Reserved Notation "x +++ y" (at level 60, right associativity).

Equations vapp {A n m} (v : vec A n) (v' : vec A m) : vec A (n + m) := {
  vnil +++ v' := v' ;
  vcons a v +++ v' := vcons a (v +++ v')
} (* Note the need for braces. *)
where "x +++ y" := (vapp x y).

(* Stating associativity however is going to be a problem. *)
Fail Lemma vapp_assoc :
  forall A n m k (v1 : vec A n) (v2 : vec A m) (v3 : vec A k),
    v1 +++ v2 +++ v3 = (v1 +++ v2) +++ v3.

(* To state it we need to use the face that addition is associative. *)
(* To leverage this we use the notion of transport: *)

Definition transport {A} {P : A -> Type} {u v} (e : u = v) : P u -> P v :=
  match e with
  | eq_refl => fun x => x
  end.

From Coq Require Import Lia.

Search ((_ + _) + _).

(* Using the Search command above you should be able to find a replacement
  for todo in the statement.
*)

Lemma vapp_assoc :
  forall A n m k (v1 : vec A n) (v2 : vec A m) (v3 : vec A k),
    v1 +++ v2 +++ v3 =
    transport (todo) ((v1 +++ v2) +++ v3).
Proof.
  (* Do you manage to do the proof? Try a bit to see the problem, if any. *)
  intros.

Abort.

(* To help fix the problem we will assume uniqueness of identity proofs. *)
(* Note that we do not actually need it. See project. *)

Axiom K : forall A (u : A) (e : u = u), e = eq_refl.

(* From it we can eliminate useless transport *)
Lemma transportK :
  forall A (u : A) (e : u = u) (P : A -> Type) (t : P u),
    transport e t = t.
Proof.
Admitted.

(* Now prove that transport commutes with vcons *)
Lemma transport_vcons :
  forall A n m e e' a (v : vec A n),
    transport e (vcons a v) = vcons a (n := m) (transport e' v).
Proof.
Admitted.

(* Let's try again *)

Lemma vapp_assoc :
  forall A n m k (v1 : vec A n) (v2 : vec A m) (v3 : vec A k),
    v1 +++ v2 +++ v3 =
    transport (todo) ((v1 +++ v2) +++ v3).
Proof.
Admitted.

(* The proof is actually doable but we see here that this is a pain. *)

(* Worse, these transports will pollute terms as well.
  Try to fix the rev_acc definition below.

  Note, you can leave underscores (_) in places you want to leave for later.
  You can use Equations? (with a question mark) to open a goal with the missing
  information to fill (proof obligations).
  Equations might solve them automatically. I recommend to use
  #[tactic=idtac] Equations?
  first, in order to see what it must solve.
*)

Fail Equations rev_acc {A n m} (v : vec A n) (acc : vec A m) : vec A (n + m) :=
  rev_acc vnil acc := acc ;
  rev_acc (vcons a v) acc := rev_acc v (vcons a acc).

(* A more practical approach to vectors is the use of subset types: *)

From Coq Require Import List.
Import ListNotations.

Definition ilist (A : Type) (n : nat) :=
  { l : list A | length l = n }.

(* Some notation so that it's nicer (feel free to change it if you don't like
  unicode or whatever).
*)
Notation "⟨ u | v ⟩" := (exist _ u v) (at level 0).

(* This "only parsing" notation is just to avoid writing an underscore
  when writing functions.
*)
Notation "⟨ u ⟩" := (⟨ u | _ ⟩) (at level 0, only parsing).

(* One lemma about equality on this structure *)

Lemma ilist_eq :
  forall A n (l l' : ilist A n),
    proj1_sig l = proj1_sig l' ->
    l = l'.
Proof.
  intros A n [l e] [l' e'] H.
  simpl in H.
  subst l'.
  f_equal.
  (* Note that besides rewrite, you can use subst x to substitute x by u
    when you have an hypothesis of the form x = u or u = x. *)
Admitted.

Definition to_ilist {A} (l : list A) : ilist A (length l) :=
  todo
.

(* We can show that they are equivalent to our other notion of vectors. *)
(* For this we simply say that there is a bijection between the two. *)

Record equiv (A B : Type) := {
  l_to_r : A -> B ;
  r_to_l : B -> A ;
  l_to_l : forall a, r_to_l (l_to_r a) = a ;
  r_to_r : forall b, l_to_r (r_to_l b) = b
}.

(* Don't hesitate to write auxiliary functions to help you. *)

Lemma equiv_ilist :
  forall A n,
    equiv (vec A n) (ilist A n).
Proof.
  intros A n.
  (* Showing you what you can do to give the equivalence nicely. *)
  (* The notation 'p lets you perform a match on the fly (when there is only one
    constructor)
  *)
  unshelve refine {|
    l_to_r v := todo ;
    r_to_l '⟨ l | e ⟩ := todo
  |}.
  - apply todo.
  - apply todo.
Defined.

(* Let's write the head function on ilist *)
Equations hd {A n} (l : ilist A (S n)) : A :=
  hd l := todo.

(* And tail. *)
Equations tl {A n} (l : ilist A (S n)) : ilist A n :=
  tl l := todo.

(* We can do append again. *)
Reserved Notation "x ⊕ y" (at level 60, right associativity).

Equations? iapp {A n m} (l : ilist A n) (l' : ilist A m) : ilist A (n + m) := {
  ⟨ l | e ⟩ ⊕ ⟨ l' | e' ⟩ := ⟨ l ++ l' ⟩
}
where "x ⊕ y" := (iapp x y).
Proof.
Admitted.

(* Wait, associativity still suffers from the same problem! *)
Fail Lemma iapp_assoc :
  forall A n m k (v1 : ilist A n) (v2 : ilist A m) (v3 : ilist A k),
    v1 ⊕ v2 ⊕ v3 = (v1 ⊕ v2) ⊕ v3.

(* The rationale here is: we don't care! We have ilist_eq that says that
  only equality of the underlying lists matters. We separate the data from
  its invariants (length).
*)

(* We can also write the nth function on ilist. *)
(* Notice how, Equations here will not figure out everything and we have to
  help it see that some cases are impossible using False_rect _ _.
*)

Equations? inth {A n} (l : ilist A n) (x : fin n) : A :=
  inth l x := todo.
Proof.
Qed.

(* Let's switch subjects a bit now. *)

(* Before, let's adjust one Equations setting. *)
Set Equations Transparent.
(* It simply says that Equations definition shouldn't be opaque anymore.
  They will behave like regular functions. This means we don't always need
  to use simp to simplify things.
*)

(* Simply typed λ-calculus *)
(* We will use dependent types to define well-typed syntax. *)

(* We define our simple types. *)
(* If it's too easy for you, you can add more stuff like pairs. *)
Inductive type := tunit | tarrow (a b : type).

Notation "A ⇒ B" := (tarrow A B) (at level 20, right associativity).

(* Open terms can have variables. We store their types in an environment. *)
(* We use vectors so it's easy to keep track of variables. *)
(* We could use lists as well. *)
Definition env := vec type.

Inductive term {n} (Γ : env n) : type -> Type :=
| tvar (x : fin n) : term Γ (vnth Γ x)
| tstar : term Γ tunit
| tlam (A : type) B (b : term (vcons A Γ) B) : term Γ (tarrow A B)
| tapp A B (f : term Γ (tarrow A B)) (u : term Γ A) : term Γ B.

Arguments tvar {n Γ}.
Arguments tstar {n Γ}.
Arguments tlam {n Γ} _ {B}.
Arguments tapp {n Γ A B}.

(* You can write your examples. Sometimes you need to give the shape of the
  context to Coq so it can figure out the length. This is annoying, but
  unification is not complete.

  Notice you can only write well-typed terms by construction.
*)

(* The example below needs some definitions above to be completed to work.
  Once that is done you should be able to safely remove the Fail.
*)
 Example test A B : term vnil _ :=
  tlam (A ⇒ B) (tlam A (tapp (tvar (Γ := vcons _ (vcons _ _)) (finS fin0)) (tvar fin0))).

(* This one is supposed to fail. *)
Fail Example test' : term vnil _ :=
  tapp tstar tstar.

(* Let us now "interpret" these terms and types into Coq (Gallina) terms. *)

(* We have to start with types, we need to give a meaning (interpretation) to
  tunit and tarrow. There should be nothing surprising with how we define them.
*)

Reserved Notation "⟦ A '⟧ty'".

Fixpoint interp_type (t : type) : Type :=
  match t with
  | tunit => unit
  | A ⇒ B => ⟦ A ⟧ty -> ⟦ B ⟧ty
  end

where "⟦ A '⟧ty'" := (interp_type A).

Eval compute in ⟦ (tunit ⇒ tunit) ⇒ tunit ⟧ty.

(* When interpreting terms, we soon see that we need to interpret variables
  somehow. For this we carry around a valuation for our environment Γ.
  It maps every variable (index) to a value of the corresponding type.
*)

Definition valuation {n} (Γ : env n) :=
  forall x, ⟦ vnth Γ x ⟧ty.

(* The empty valuation *)
Definition ρ₀ : valuation vnil :=
  fun x => match x with end.

(* Extension of a valuation with a new value. *)
Equations extend {n Γ A} (ρ : valuation (n := n) Γ) (a : ⟦ A ⟧ty) : valuation (vcons A Γ) :=
extend ρ a (fin0) := a;   
extend ρ a (finS x) := ρ x.

(* We are now ready to interpret terms! *)

Reserved Notation "⟦ t | r '⟧tm'".

Equations interp {n Γ A} (t : term (n := n) Γ A) (ρ : valuation Γ) : ⟦ A ⟧ty := {
  ⟦ tstar | ρ ⟧tm := tt;
  ⟦ tvar x | ρ ⟧tm := ρ x;
  ⟦ tlam a b | ρ ⟧tm := fun x => ⟦ b | extend ρ x ⟧tm;
  ⟦ tapp a b | ρ ⟧tm := ⟦ a | ρ ⟧tm ⟦ b | ρ ⟧tm
}
where "⟦ t | r '⟧tm'" := (interp t r).

(* We can test on a few examples and see them get normalised. *)
(* Remove Fail when you reach this. *)

 Eval compute in ⟦ test tunit tunit | ρ₀ ⟧tm.

 Eval compute in ⟦ tapp (test _ _) (test tunit tunit) | ρ₀ ⟧tm.


(* Let us move to another (but similar) notion of evaluation. *)
(* We cosnider monoids and their equational theory.
  Like how simply typed λ-calculus has β-reduction, monoids are associative.

  We will use so-called "free monoids" ie monoids with no extra structure.
  The type monoid A V below contains values in A, variables in V, a neutral
  element ε and a monoid operation _ ⋅ _.
*)

Inductive monoid (A V : Type) :=
| mvar (x : V)
| matom (a : A)
| memp
| mop (u v : monoid A V).

Arguments mvar {A V}.
Arguments matom {A V}.
Arguments memp {A V}.
Arguments mop {A V}.

Notation "'ε'" := (memp).
Notation "u ⋅ v" := (mop u v) (at level 60, right associativity).

(* We will use string for variables in our examples *)
From Coq Require Import String.

Example ex1 : monoid nat string :=
  ((mvar "x" ⋅ matom 3) ⋅ ε ⋅ (mvar "y" ⋅ matom 7))%string.

Example ex2 : monoid nat string :=
  (mvar "x" ⋅ matom 3 ⋅ mvar "y" ⋅ matom 7)%string.

(* Like we did for λ-calculus, we can evaluate these expressions by giving
  an interpretation to variables and obtaining values of type list A.
  Indeed, once you eliminate variables, and up-to associativity, these are
  the only inhabitants of the free monoid.
*)

Definition mvaluation A V := V -> list A.

(* Define the following interpretation using the ++ operator on lists. *)
Fixpoint simpl_eval {A V} (e : monoid A V) (ρ : mvaluation A V) : list A :=
  todo.

(* For our examples, we can use the following valuation. *)
(* It's not very efficient, but it suffices for us. *)

Example myval : mvaluation nat string :=
  fun x =>
    match x with
    | "x" => [ 0 ; 1 ]
    | "y" => [ 2 ]
    | _ => []
    end%string.

Eval compute in simpl_eval ex1 myval.

(* ex1 and ex2 are the same up-to associativity, so their evaluations are
  equal.
*)
Check eq_refl : simpl_eval ex1 myval = simpl_eval ex2 myval.

(* We said we considered inhabitants of the free monoid modulo associativity.
  For now we can evaluate the term and indeed get that.
  But what if we wanted to do that while keeping uninterpreted variables?
*)

(* We can define this associativity (+ neutral ε) relation. *)

Reserved Notation "u ~ v" (at level 90).

Inductive monoid_eq {A V} : monoid A V -> monoid A V -> Prop :=

(* ε is neutral *)

| m_neutral_l : forall u, ε ⋅ u ~ u

| m_neutral_r : forall u, u ⋅ ε ~ u

(* ⋅ is associative *)

| m_assoc : forall u v w, (u ⋅ v) ⋅ w ~ u ⋅ v ⋅ w

(* Equivalence rules *)

| m_refl : forall u, u ~ u

| m_sym : forall u v, u ~ v -> v ~ u

| m_trans : forall u v w, u ~ v -> v ~ w -> u ~ w

(* Congruence rule *)

| m_cong : forall u u' v v', u ~ u' -> v ~ v' -> u ⋅ v ~ u' ⋅ v'

where "u ~ v" := (monoid_eq u v).

Lemma ex1_eq_ex2 : ex1 ~ ex2.
Proof.
Admitted.

(* Another method would be to be able to normalise expressions in the free
  monoid. For this we use a method called normalisation by evaluation (NbE).

  We begin by writing an evaluation function as before, but this time we don't
  want to interpret variables, so instead, we need to handle them as values.
  We say that we "reflect" variables as values.

  Once we do that evaluation is straightforward and doesn't require any
  valuation.
*)

Definition value A V := list (A + V).

(* To understand what the + above is you can run Locate: *)
Locate "+".
(* You should guess that it is the sum type. *)
Print sum.
(* Now you can see that you inhabit it using inl and inr. *)

Fixpoint eval {A V} (e : monoid A V) : value A V :=
  todo.

(* In order to get back a normal form, we need to be able to turn values
  back into free monoid expressions. This process is called reification.
*)

Fixpoint reify {A V} (v : value A V) : monoid A V :=
  todo.

(* Test it on a few examples. If you see trailing ε, then don't throw away that
  version, we might need it later, but try to define it without trailing ε.
*)

(* Normalisation by evaluation is just the process of evaluating the expression
  and then reifying it back to its original syntax.
*)

Definition nbe {A V} (e : monoid A V) : monoid A V :=
  reify (eval e).

(* We can test it on examples. *)

Eval compute in nbe ex1.

(* ex1 and ex2 indeed have the same normal form! *)
Check eq_refl : nbe ex1 = nbe ex2.

(* We can even prove that it's always the case. *)

Lemma eval_sound :
  forall A V (u v : monoid A V),
    u ~ v ->
    eval u = eval v.
Proof.
Admitted.

Lemma nbe_sound :
  forall A V (u v : monoid A V),
    u ~ v ->
    nbe u = nbe v.
Proof.
Admitted.

Lemma nbe_self :
  forall A V (u : monoid A V),
    u ~ nbe u.
Proof.
Admitted.

Lemma nbe_complete :
  forall A V (u v : monoid A V),
  nbe u = nbe v ->
  u ~ v.
Proof.
Admitted.

(* Now, thanks to this we can decide equality in the monoid much faster! *)

Lemma re_ex1_eq_ex2 : ex1 ~ ex2.
Proof.
Admitted.

(* Now, let's switch subject one last time and go back to well-founded
  recursion. This time using Equations.
*)

(* We can look at the Hardt function. It is defined as follows:

  hardt 0 := 0
  hardt 1 := 1
  hardt n := hardt (n - 1) + hardt (hardt (n-1) - hardt (n-2))      when n > 1

  We can actually prove that this is the identity function.
  In fact we will even need to know this fact to get Equations to accept it.
*)

(* Hint: A useful notation to get out of a subset type. *)
Notation "x .1" := (proj1_sig x) (at level 11).

(* by wf n lt says we do well-founded induction on n using lt (<) as an order. *)
Equations? hardt (n : nat) : todo by wf n lt :=
  hardt n := todo.
Proof.
Defined.

(* If you're brave enough, you can look into a similar function for which
  termination is much harder. :)
*)

(* The McCarthy 91 function is defined as follows:

  m91 n := n - 10                when  n > 100
  m91 n := m91 (m91 (n + 11))    otherwise

  It is it interesting because for n ≤ 100 it actually always produces 91.
  So we could actually write:

  m91 n := n - 10                when  n > 100
  m91 n := 91                    otherwise

  Let's say for the sake of fun that we want to write it as specified.
  This is a tricky exercise.
*)

(* Here are some useful tools for this. *)

From Coq Require Import Arith.

(* This gives us notations like "n <? m" to check whether n < m. *)

(* Inside proofs you might want to use stuff like

  destruct (le_gt_dec n m) as [h | h].

  to decide locally whether n is smaller or bigger than m.
*)

(* The following is a trick to let Equations retain equalities inside a pattern
 matching. Otherwise, we might be missing some information in the obligations.
*)

Definition inspect {A} (a : A) : {b | a = b} :=
  exist _ a eq_refl.

Notation "x 'eq:' p" := (exist _ x p) (only parsing, at level 20).

(* Here is a silly example *)

Equations? foo (n : nat) : { b : bool | n < 27 <-> b = true } :=
  foo n with inspect (n <? 27) := {
  | true eq: e => ⟨ true ⟩
  | false eq: e => ⟨ false ⟩
  }.
Proof.
  (* Notice how we have access to e in the goals. *)
  - split. 1: auto.
    intros _. apply Nat.ltb_lt in e. assumption.
  - split. 2: discriminate.
    intro h. apply Nat.ltb_ge in e. lia.
Qed.

(* One last hint: you will need your own order. *)

Definition lt91 (n m : nat) : Prop :=
  todo.

(* And prove it is well founded. *)

#[local] Instance wf_lt91 : WellFounded lt91.
Proof.
Admitted.

(* Let us define the function now. *)

Equations? m91 (n : nat) : todo by wf n lt91 :=
  m91 n := todo.
Proof.
Defined.