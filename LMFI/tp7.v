Require Import List.
Import ListNotations.

Inductive alpha := M | I | U.

Definition word := list alpha.

Inductive lang : word -> Prop :=
| axiom : lang [M;I]
| rule1 x : lang (x ++ [I]) -> lang (x ++ [I;U])
| rule2 x : lang ([M] ++ x) -> lang ([M] ++ x ++ x)
| rule3 x y : lang (x ++ [I;I;I] ++ y) -> lang (x ++ [U] ++ y)
| rule4 x y : lang (x ++ [U;U] ++ y) -> lang (x ++ y).

Check List.hd.
Check List.hd_error.


Lemma startM (w:word) : lang w -> (List.hd_error w) = Some M.
Proof.
  intro.
  induction H; trivial.
  unfold List.hd_error.
  destruct x; simpl in *; trivial.
  - destruct x; simpl in *.
    + discriminate.
    + apply IHlang.
  - destruct x; simpl in *.
    + discriminate.
    + apply IHlang.
Qed.

Lemma startMexists (w:word): lang w -> exists t, w=M::t.
Proof.
  intro.
  apply startM in H.
  destruct w.
  unfold hd_error in *.
  discriminate.
  simpl in *.
  injection H as ->.
  exists w.
  trivial.
Qed.


Inductive Z3 := Z0 | Z1 | Z2.

Definition succ (n:Z3) := 
  match n with 
  |Z0 => Z1
  |Z1 => Z2
  |Z2 => Z0
  end
.


Definition add (x y:Z3) :=
  match x with 
  |Z0 => y 
  |Z1 => succ y 
  |Z2 => succ (succ y)
  end
.
 
Lemma add_comm (x y:Z3) : add x y = add y x.
Proof.
  destruct x,y; simpl; trivial.
Qed.

Lemma add_assoc (x y z:Z3) : add x (add y z) = add (add x y) z.
Proof.
  destruct x,y,z; simpl; trivial.
Qed.

Lemma add_Z0 (x:Z3) : add x Z0 = x.
Proof.
  destruct x; simpl; trivial.
Qed.


Lemma notZ0 (z:Z3) : z<>Z0 -> add z z <> Z0.
Proof.
  destruct z; simpl; trivial; discriminate.
Qed.


Fixpoint occurI3 (w:word) := 
  match w with 
  |[] => Z0
  |I::t => add Z1 (occurI3 t)
  |_::t => occurI3 t
  end
.


Lemma occurI3Nil : occurI3 [] = Z0.
Proof.
  unfold occurI3.
  trivial.
Qed.
  
Lemma add_succ (x y:Z3) : succ (add x y) = add (succ x) y.
Proof.
  destruct x,y; trivial.
Qed.

Lemma conc_occurI3 (v w:word) : occurI3 (v ++ w) = add (occurI3 v) (occurI3 w).
Proof.
  destruct v,w; simpl; trivial;destruct a; simpl.
Qed.

Lemma distr_occurI3 (v w:word) : occurI3 (v ++ w) = add (occurI3 v) (occurI3 w).
Proof.
  induction v; simpl.
  - trivial.
  - destruct a. 
    + apply IHv.
    + rewrite <- add_succ. 
    rewrite occurI3Nil. rewrite add_Z0.
  






