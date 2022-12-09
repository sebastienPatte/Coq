(* begin hide *)

Unset Implicit Arguments.
Set Asymmetric Patterns.
Axiom todo : forall {A}, A.
Ltac todo := apply todo.
(* end hide *)

Class Monoid {A:Type} (dot : A -> A -> A) (one : A) : Type := 
  { dot_assoc : forall x y z : A, dot x (dot y z) = dot (dot x y) z;
    one_left : forall x, dot one x = x;
    one_right : forall x, dot x one = x }.

Generalizable Variables A dot one.

(** %\end{frame}\begin{frame}\frametitle{Generic notations}%
   Global names for parameters: *)

Definition monop `{Monoid A dot one} := dot.
Definition monunit `{Monoid A dot one} := one.

(** Generic notations: *)

Infix "*" := monop.
Notation "1" := monunit.

Section Reification.
  Context `{Monoid A dot one}.

  Inductive MonoidExpr A :=
  | monoid_cst : A -> MonoidExpr A (* for any constant not recognized as the unit or operation *)
  | monoid_unit : MonoidExpr A
  | monoid_op : MonoidExpr A -> MonoidExpr A -> MonoidExpr A.

  Fixpoint interp (e : MonoidExpr A) : A :=
    match e with
    | monoid_cst x => x
    | monoid_unit => one
    | monoid_op x y => dot (interp x) (interp y)
    end.

  Class ReifyExpr (a : A) :=
    { reified_expr : MonoidExpr A;
      reified_correct : interp reified_expr = a }.

  Instance reify_var (a : A) : ReifyExpr a | 100 := {| reified_expr := monoid_cst _ a |}.
  Proof. reflexivity. Defined.

  Instance reify_op (a b : A) (ra : ReifyExpr a) (rb : ReifyExpr b) : ReifyExpr (dot a b) := 
    {| reified_expr := monoid_op _ (reified_expr (a:=a)) (reified_expr (a:=b)) |}.
  Proof. simpl. rewrite !reified_correct. reflexivity. Defined.

  Instance reify_unit : ReifyExpr one :=
    {| reified_expr := monoid_unit _ |}.
  Proof. simpl. reflexivity. Defined.

  Fixpoint simplify_expr (x : MonoidExpr A) : MonoidExpr A :=
    match x with
    | monoid_op x y =>
      match simplify_expr x, simplify_expr y with
      | monoid_unit, y => y
      | x, monoid_unit => x
      | x, y => monoid_op _ x y
      end
    | x => x
    end.

  (* Show it is correct: it should only apply valid laws of the monoid *)
  Lemma simplify_expr_correct (e : MonoidExpr A) : interp (simplify_expr e) = interp e.
  Proof.
    induction e; simpl; auto.
    destruct (simplify_expr e1) eqn:eq1;
    destruct (simplify_expr e2) eqn:eq2;
    rewrite <- IHe1, <- IHe2;
    simpl in *; auto. subst; auto. now rewrite one_right.
    now rewrite one_left.
    now rewrite one_left.
    now rewrite (one_left (one:=one)).
    now rewrite (one_right (one:=one)).
  Qed.
    
  (* Using correctness, show that simplifying a reified expression for [a]
     and interpreting it back gives a term equal to [a] *)
  Lemma simplify_monoid (a : A) {e : ReifyExpr a} : a = interp (simplify_expr reified_expr).
  Proof. 
    rewrite simplify_expr_correct.
    now rewrite reified_correct.
  Qed.

  (** This proof script should go through once the above is finished. *)
  Example simpl_goal (x : A) : monop x monunit = x.
  Proof. pose proof (simplify_monoid (monop x monunit)) as Heq.
    simpl in Heq. assumption. Qed.

End Reification.v