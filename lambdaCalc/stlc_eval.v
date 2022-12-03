Require Import Option.
Require Import List.
Require Import MyTactics.
Require Import LambdaCalculusSyntax.
Require Import LambdaCalculusFreeVars.
Require Import LambdaCalculusBigStep.

(* We now wish to define an interpreter for the lambda-calculus. In other
   words, whereas [ebigcbv] is a relation, we now wish to define a function
   [interpret] whose graph is the relation [ebigcbv]. *)

(* At the moment, our lambda-calculus is pure (every value is a function)
   so the interpreter cannot encounter a runtime error. *)

(* -------------------------------------------------------------------------- *)

(* We might naively wish to write the following code, which Coq rejects,
   because this function is not obviously terminating. (Exercise: which
   recursive call is the culprit?) Indeed, an interpreter for the untyped
   lambda-calculus does not always terminate: there are lambda-terms whose
   evaluation diverges. (Exercise: exhibit a term that reduces to itself
   in one or more reduction steps. Prove in Coq that this is the case.) *)

Fail Fixpoint interpret (e : cenv) (t : term) : cvalue :=
  match t with
  | Var x =>
      nth x e dummy_cvalue
        (* dummy is used when x is out of range *)
  | Lam t =>
      Clo t e
  | App t1 t2 =>
      let cv1 := interpret e t1 in
      let cv2 := interpret e t2 in
      match cv1 with Clo u1 e' =>
        interpret (cv2 :: e') u1
      end
  | Let t1 t2 =>
      let cv1 := interpret e t1 in
      interpret (cv1 :: e) t2
  end.

(* -------------------------------------------------------------------------- *)

(* There are several potential solutions to the above problem. One solution
   would be to write code in (some implementation of) the partiality monad.
   (See Dagand's lectures.) The solution proposed here is to parameterize
   the function [interpret] with a natural integer [n], which serves as an
   amount of "fuel" (or "effort") that we are willing to invest before we
   give up. Thus, termination becomes obvious. The downside is that the
   interpreter can now fail (which means "not enough fuel"). Fortunately,
   given enough fuel, every terminating term can be evaluated. *)

(* For Coq to accept the following definition, the fuel [n] must decrease at
   every recursive call. We might wish to be more precise and somehow explain
   that [n] needs to decrease only at the third recursive call in the case of
   [App]lications. That would require defining a lexicographic ordering on the
   pair [n, t], arguing that this ordering is well-founded, and defining
   [interpret] by well-founded recursion. This can be done in Coq but is more
   complicated, so (here) not worth the trouble. *)

Fixpoint interpret (n : nat) e t : option cvalue :=
  match n with
  | 0   => None (* not enough fuel *)
  | S n =>
      match t with
      | Var x     => Some (nth x e dummy_cvalue)
      | Lam t     => Some (Clo t e)
      | App t1 t2 =>
          interpret n e t1 >>= fun cv1 =>
          interpret n e t2 >>= fun cv2 =>
          match cv1 with Clo u1 e' =>
            interpret n (cv2 :: e') u1
          end
      | Let t1 t2 =>
          interpret n e t1 >>= fun cv1 =>
          interpret n (cv1 :: e) t2
  end end.

(* -------------------------------------------------------------------------- *)

(* The interpreter is correct with respect to the big-step semantics. *)

Lemma interpret_ebigcbv:
  forall n e t cv,
  interpret n e t = Some cv ->
  fv (length e) t ->
  wf_cenv e ->
  ebigcbv e t cv.
Proof.
  (* The definition of [interpret] is by induction on [n], so this proof
     must be by induction on [n] as well. *)
  induction n; destruct t; simpl; intros;
  fv; unpack; injections; subst;
  try solve [ congruence ].
  (* Var *)
  { econstructor; eauto. }
  (* Lam *)
  { econstructor; eauto. }
  (* App *)
  { repeat invert_bind_Some.
    (* Every cvalue is a closure. Name the components of the closure
       obtained by interpreting [t1]. *)
    match goal with h: interpret _ _ t1 = Some ?cv |- _ =>
      destruct cv as [ t' e' ]
    end.
    (* The goal follows. *)
    econstructor; eauto 11 with wf_cvalue. }
  (* Let *)
  { invert_bind_Some.
    econstructor; eauto with wf_cvalue. }
Qed.

(* A simplified corollary, where [t] is closed and is therefore evaluated
   under the empty environment, and where we conclude with a [bigcbv]
   judgement. *)

Lemma interpret_bigcbv_nil:
  forall n t cv,
  interpret n nil t = Some cv ->
  closed t ->
  bigcbv t (decode cv).
Proof.
  eauto using ebigcbv_bigcbv_nil, interpret_ebigcbv with wf_cvalue.
Qed.

(* -------------------------------------------------------------------------- *)

(* The interpreter is monotonic with respect to the amount of fuel that is
   provided: the more fuel, the better (that is, the more defined the result). *)

Lemma interpret_monotonic:
  forall n1 n2 e t,
  n1 <= n2 ->
  less_defined (interpret n1 e t) (interpret n2 e t).
Proof.
  (* This series of tactics get rid of the easy cases: *)
  induction n1; destruct t; simpl; intros;
  (* [less_defined None _] is always true. *)
  eauto with less_defined;
  (* If [S n1 <= n2], then [n2] must be a successor. *)
  (destruct n2; [ lia |]); simpl;
  (* [less_defined] is reflexive. *)
  eauto with less_defined.

  (* Two more complex cases remain, namely [App] and [Let]. Probably
     the proof could be further automated, but I did not try. *)
  (* App *)
  { eapply prove_less_defined_bind.
    { eauto using le_S_n. }
    { intros _ [ t' e' ]. (* destruct the closure produced by [t1] *)
      eapply prove_less_defined_bind; eauto using le_S_n. }
  }
  (* Let *)
  { eauto 6 using le_S_n with less_defined. }
Qed.

(* A reformulation. *)

Lemma interpret_monotonic_corollary:
  forall n1 n2 e t cv,
  interpret n1 e t = Some cv ->
  n1 <= n2 ->
  interpret n2 e t = Some cv.
Proof.
  generalize interpret_monotonic. unfold less_defined. eauto.
Qed.

(* -------------------------------------------------------------------------- *)

(* The interpreter is complete with respect to the big-step semantics
   [ebigcbv]. That is, given enough fuel, and given a term whose value is
   [cv], it will compute [cv]. *)

Lemma ebigcbv_interpret:
  forall e t cv,
  ebigcbv e t cv ->
  exists n,
  interpret n e t = Some cv.
Proof.
  (* We can see, in the proof, that the necessary amount of fuel, [n], is
     the height of the derivation of the judgement [ebigcbv e t cv].
     Indeed, at every [App] or [Let] node, we count 1 plus the maximum
     amount of fuel required by our children. *)
  induction 1; intros; subst.
  (* EBigcbvVar *)
  { exists 1. eauto. }
  (* EBigcbvLam *)
  { exists 1. eauto. }
  (* EBigcbvApp *)
  { destruct IHebigcbv1 as [ n1 ? ].
    destruct IHebigcbv2 as [ n2 ? ].
    destruct IHebigcbv3 as [ n3 ? ].
    eexists (S (max (max n1 n2) n3)). simpl.
    eauto 6 using prove_bind_Some, interpret_monotonic_corollary with lia. }
  (* EBigcbvLet *)
  { destruct IHebigcbv1 as [ n1 ? ].
    destruct IHebigcbv2 as [ n2 ? ].
    eexists (S (max n1 n2)). simpl.
    eauto using prove_bind_Some, interpret_monotonic_corollary with lia. }
Qed.

(* The interpreter is complete with respect to the big-step semantics
   [bigcbv]. That is, given enough fuel, and given a term [t] whose value is
   [v], it will compute a cvalue [cv] which decodes to [v]. We state this in
   the case where [t] is closed and is therefore evaluated under the empty
   environment. *)

Lemma bigcbv_interpret_nil:
  forall t v,
  bigcbv t v ->
  closed t ->
  exists n cv,
  interpret n nil t = Some cv /\ decode cv = v.
Proof.
  intros.
  edestruct bigcbv_ebigcbv_nil; eauto. unpack.
  edestruct ebigcbv_interpret; eauto.
Qed.

