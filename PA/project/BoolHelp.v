Require Import ZArith Arith Bool Lia.

Lemma ltb_correct (a b:nat) : a < b -> a <? b = true.
  apply Nat.ltb_lt; assumption.
Qed.

Lemma ltb_complete (a b:nat) : a <? b = true -> a < b.
  apply Nat.ltb_lt; assumption.
Qed.

Lemma ltb_imp_leb (i j :nat) : (i <? j) = true -> (i <=? j) = true.
Proof.
  intro.
  rewrite Nat.leb_le.
  rewrite Nat.ltb_lt in H.
  apply Nat.lt_le_incl. 
  assumption.
Qed.

Lemma ltb_trans (i j n :nat) : (i <? j) = true /\ (j <? n) = true -> (i <? n) = true.
Proof.
  intros.
  destruct H.
  rewrite Nat.ltb_lt in H.
  rewrite Nat.ltb_lt in H0.
  rewrite Nat.ltb_lt.
  eapply Nat.lt_trans with (m:= j); assumption.
Qed.

Lemma leb_trans (i j n :nat) : (i <=? j) = true /\ (j <=? n) = true -> (i <=? n) = true.
Proof.
  intros.
  destruct H.
  rewrite Nat.leb_le in H.
  rewrite Nat.leb_le in H0.
  rewrite Nat.leb_le.
  eapply Nat.le_trans with (m:= j); assumption.
Qed.

Lemma ltb_leb_trans (i j n :nat) : (i <? j) = true /\ (j <=? n) = true -> (i <? n) = true.
Proof.
  intros.
  destruct H.
  rewrite Nat.ltb_lt in H.
  rewrite Nat.leb_le in H0.
  rewrite Nat.ltb_lt.
  apply Nat.lt_le_trans with (m:= j); assumption.
Qed.

Lemma ltb_leb_incl (i j :nat) : (i <? j) = true -> (i <=? j) = true.
Proof.
  rewrite Nat.ltb_lt.
  rewrite Nat.leb_le.
  apply Nat.lt_le_incl.
Qed.


(* Proof irrelevance on booleans *)

Lemma b_dec : forall (b1 b2 : bool), b1 = b2 \/ b1 <> b2.
  Proof.
    intros.
    destruct b1,b2; intuition.
  Qed.

  Local Definition comp [A] [x y y':A] (eq1:x = y) (eq2:x = y') : y = y' :=
    eq_ind _ (fun a => a = y') eq2 _ eq1.

    Local Definition trans_sym_eq [A] (x y:A) (u:x = y) : comp u u = eq_refl y.
  Proof.
    case u; trivial.
  Qed.

  Local Definition nu [x y:bool] (u:x = y) : x = y :=
  match b_dec x y with     
    | or_introl eqxy => eqxy 
    | or_intror neqxy => False_ind _ (neqxy u)
  end.

  Local Definition nu_constant [x y:bool] (u v:x = y) : nu u = nu v.
    unfold nu.
    destruct (b_dec x y) as [Heq|Hneq].
    - reflexivity.
    - case Hneq; trivial.
  Qed.

  Local Definition nu_inv [x y:bool] (v:x = y) : x = y := comp (nu (eq_refl x)) v.

  Local Definition nu_left_inv [x y:bool] (u:x = y) : nu_inv (nu u) = u.
  Proof.
    case u; unfold nu_inv.
    case eq_refl.
    apply trans_sym_eq.
  Qed.

  Lemma bool_irrel (x y:bool) (p1 p2:x = y) : p1 = p2.
  Proof.
    elim (nu_left_inv p1).
    elim (nu_left_inv p2).
    elim nu_constant with x y p1 p2.
    reflexivity.
  Qed.

  
#[export] Hint Resolve leb_complete : core. 
#[export] Hint Resolve leb_correct : core. 
#[export] Hint Resolve ltb_correct : core. 
#[export] Hint Resolve ltb_complete : core.
#[export] Hint Resolve Nat.ltb_lt : core.
#[export] Hint Resolve Nat.sub_0_r Nat.lt_le_incl ltb_imp_leb ltb_trans leb_trans ltb_leb_trans: core.