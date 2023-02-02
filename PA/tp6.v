From Coq.Logic Require Import ConstructiveEpsilon.
Require Import Lia Arith List Bool.

(** ** Classical logical axioms  *)

Definition LEM := forall P, P \/ ~ P.
Definition DNE := forall P, ~~P -> P.
Definition CP : Prop := forall X Y : Prop, (~Y -> ~X) -> X -> Y.        (* contraposition *)
Definition Peirce := forall P Q : Prop, ((P -> Q) -> P) -> P.

Goal LEM -> DNE.
unfold LEM, DNE.
intros.
specialize (H P).
unfold not in H0.
destruct H.
- assumption.
- specialize (H0 H).
  contradiction.
Qed.

Goal DNE -> CP. 
unfold DNE, CP.
intros.
  apply (H Y).
  unfold not in *.
  intros.
  apply H0.
  apply H2.
  assumption.
Qed.

Goal CP -> Peirce. 
	unfold CP, Peirce.
  intros.

  specialize (H P Q) as HPQ.
  intros.
  unfold not in *.
Admitted.


Lemma nnLEM : forall P, ~~ (P \/ ~ P).
intros.
  unfold not.
  intro.
  apply H.
  right.
  intro.
  apply H.
  left.
  assumption.
Qed.

Goal forall p : nat -> Prop, (exists n, p n) -> ~~ exists n, p n /\ forall k, p k -> n <= k.
  intros.
  unfold not.
  intros.
  apply H0.
  destruct H.
  exists x.
  split.
  assumption.
  intros.

Admitted.

Goal Peirce -> forall philosophers_stone infinite_gold : Prop, philosophers_stone \/ (philosophers_stone -> infinite_gold). Admitted.

Goal Peirce -> LEM. 
  unfold Peirce, LEM.
  intros.
Admitted.

Definition DGP := forall P Q : Prop, (P -> Q) \/ (Q -> P).
Definition WLEM := forall P, ~~P \/ ~ P.

(* Optional *) Goal LEM -> DGP. Admitted.

(* Optional *) Goal DGP -> WLEM. Admitted.

Definition IP := forall (P : Prop), forall p : nat -> Prop, (P -> exists n, p n) -> exists n, P -> p n.

(* Optional *) Goal LEM -> IP. Admitted.

(* Decidability, semi-decidability *)

Definition semi_decidable {X} (p : X -> Prop) :=
  exists f : X -> nat -> bool, forall x, p x <-> exists n, f x n = true.

Definition co_semi_decidable {X} (p : X -> Prop) :=
  exists f : X -> nat -> bool, forall x, p x <-> forall n, f x n = false.

Definition decidable {X} (p : X -> Prop) :=
  exists f : X -> bool, forall x, p x <-> f x = true.

Lemma decidable_semi_decidable {X} (p : X -> Prop) :
  decidable p -> semi_decidable p.
  unfold decidable, semi_decidable.
  intros.
  destruct H.
  unfold iff in H.
  

  exists (fun x0 n => x x0).
  


Admitted.

(*

    LEM --> DGP --> WLEM  
     |               |
     |               |
     v               v
    LPO     -->    WLPO   -->   LLPO
     ^               ^
     |               |
     v               v
  MP /\ WLPO     PFP /\ LLPO

     ^
     |
     
  MP /\ IP

 *)

Definition LPO := forall f : nat -> bool, (exists n, f n = true) \/ ~ (exists n, f n = true).
Definition WLPO := forall f : nat -> bool, (forall n, f n = false) \/ ~ (forall n, f n = false).

Lemma forall_neg_exists_iff (f : nat -> bool) :
  (forall n, f n = false) <-> ~ exists n, f n = true.
Proof.
  unfold iff.
  split; intro.
  - unfold not.
    intro.
    destruct H0.
    specialize (H x).
    rewrite H0 in H.
    inversion H.
  - unfold not in H.
    intro.
    
Admitted.

Goal LEM -> LPO.
  unfold LEM,LPO.
  intros.
  specialize (H (exists n : nat, f n = true)).
  assumption.
Qed.

Goal WLEM -> WLPO.
  unfold WLEM, WLPO.
  intros.
  specialize (H (forall n : nat, f n = false)).

  destruct H.
  - eapply nnLEM.
  - right.
    assumption.

    
Admitted.

Goal LPO -> WLPO. Admitted.

Definition LPO_semidecidable := forall X (p : X -> Prop), semi_decidable p -> forall x, p x \/ ~ p x.

Lemma LPO_semidecidable_iff :
  LPO <-> LPO_semidecidable.
Proof.
  split.
  - intros H X p [f Hf] x.
    rewrite Hf. eapply H.
  - intros H f.
    eapply (H unit (fun _ => exists n, f n = true)).
    exists (fun _ => f). cbv. intuition. econstructor.
Qed.

Definition WLPO_semidecidable := forall X (p : X -> Prop), semi_decidable p -> forall x, ~ p x \/ ~~ p x.

Goal WLPO <-> WLPO_semidecidable.
Admitted.

Definition WLPO_cosemidecidable := forall X (p : X -> Prop), co_semi_decidable p -> forall x, p x \/ ~ p x.

Goal WLPO_cosemidecidable <-> WLPO_semidecidable.
Admitted.

Definition MP := forall f : nat -> bool, ~~ (exists n, f n = true) -> exists n, f n = true.

Goal LPO <-> MP /\ WLPO. Admitted.

Goal IP -> MP -> LPO. Admitted.

(** ** Choice axioms *)

(* (** ** Provable choice axioms  *) *)

Definition AC_on X Y :=
  forall R : X -> Y -> Prop, (forall x, exists y, R x y) -> exists f : X -> Y, forall x, R x (f x).

Definition AC := forall X Y, AC_on X Y.

Lemma AC_iff_commute :
  AC <-> forall X (A : X -> Type), (forall x, inhabited (A x)) -> inhabited (forall x, A x).
Proof.
  split.
  - intros ac X A HA.
    destruct (ac X {x & A x} (fun x '(existT _ x' ax) => x = x')) as [f Hf].
    all: admit.
  - intros H X Y R Htot.
Admitted.

Definition UNIF_on X Y := forall R : X -> Y -> Prop,
  (forall x, exists y, R x y) -> exists R' : X -> Y -> Prop, (forall x y, R' x y -> R x y) /\ (forall x, exists! y, R' x y).

Definition AUC_on X Y :=
  forall R : X -> Y -> Prop, (forall x, exists! y, R x y) -> exists f : X -> Y, forall x, R x (f x).

Definition AC_0_0 :=
  AC_on nat nat.

Definition AC_1_0 :=
  AC_on (nat -> nat) nat.

Definition ADC_on X := forall R : X -> X -> Prop, forall x0, (forall x, exists x', R x x') -> exists f : nat -> X, f 0 = x0 /\ forall n, R (f n) (f (S n)).

Definition ADC := forall X, ADC_on X.
Definition ACC := forall X, AC_on nat X.

Goal forall X Y,
  AC_on X Y <-> AUC_on X Y /\ UNIF_on X Y.
Proof. Admitted.


(** ** Extensionality axioms  *)

Definition Fext := forall X Y (f g : X -> Y), (forall x, f x = g x) -> f = g.
Definition Pext := forall P Q : Prop, P <-> Q -> P = Q.
Definition hProp (P : Type) := forall x1 x2 : P, x1 = x2.
Definition PI := forall P : Prop, hProp P.

Lemma Pext_to_PI : Pext -> PI. Admitted.

Lemma hProp_disj (P Q : Prop) :
  hProp P -> hProp Q -> ~ (P /\ Q) -> hProp (P \/ Q).
Proof. Admitted.

Lemma Fext_hProp_neg P :
  Fext -> hProp (~ P).
Proof.
  intros fext H1 H2.
  eapply fext. intros x. exfalso. tauto.
Qed.

Lemma Fext_hProp_disj (P : Prop) :
  Fext -> hProp P -> hProp (P \/ ~ P).
Proof.
  intros. now eapply hProp_disj; [ | eapply Fext_hProp_neg | ].
Qed.



Lemma Diaconescu :
  (forall X Y, AC_on X Y) -> Fext -> Pext -> LEM.
Proof.
  intros C fext pext P.
  pose (U (x : bool) := x = true \/ P).
  pose (V (x : bool) := x = false \/ P).
  destruct (C ({ p : bool -> Prop | p = U \/ p = V}) bool (fun p b => (proj1_sig p b))) as [f Hf].
  - admit.
  - pose proof (Hf (exist _ U (or_introl eq_refl))) as H1.
    pose proof (Hf (exist _ V (or_intror eq_refl))) as H2. cbn in *.
    admit.
Admitted.


(* bijection from nat * nat to nat *)
Definition embed '(x, y) : nat := 
  y + (nat_rec _ 0 (fun i m => (S i) + m) (y + x)).

(* bijection from nat to nat * nat *)
Definition unembed (n : nat) : nat * nat := 
  nat_rec _ (0, 0) (fun _ '(x, y) => match x with S x => (x, S y) | _ => (S y, 0) end) n.

Lemma embedP {xy: nat * nat} : unembed (embed xy) = xy.
Proof.
  assert (forall n, embed xy = n -> unembed n = xy).
    intro n. revert xy. induction n as [|n IH].
      intros [[|?] [|?]]; intro H; inversion H; reflexivity.
    intros [x [|y]]; simpl.
      case x as [|x]; simpl; intro H.
        inversion H.
      rewrite (IH (0, x)); [reflexivity|].
      inversion H; simpl. rewrite Nat.add_0_r. reflexivity.
    intro H. rewrite (IH (S x, y)); [reflexivity|]. 
    inversion H. simpl. rewrite Nat.add_succ_r. reflexivity.
  apply H. reflexivity.
Qed.

Lemma unembedP {n: nat} : embed (unembed n) = n.
Proof.
  induction n as [|n IH]; [reflexivity|].
  simpl. revert IH. case (unembed n). intros x y.
  case x as [|x]; intro Hx; rewrite <- Hx; simpl.
    rewrite Nat.add_0_r. reflexivity.
  rewrite ?Nat.add_succ_r. simpl. rewrite ?Nat.add_succ_r. reflexivity. 
Qed.
Arguments embed : simpl never.


Module EmbedNatNotations.
  Notation "âŸ¨ a , b âŸ©" := (embed (a, b)) (at level 0).
  Notation "'fun!' 'âŸ¨' x ',' y 'âŸ©' '=>' b" := (fun p => let (x,y) := unembed p in b) (at level 30, b at level 200).
End EmbedNatNotations.

Import EmbedNatNotations.

Lemma decidable_AC X :
  forall R : X -> nat -> Prop, decidable (uncurry R) -> (forall x, exists n, R x n) -> exists f, forall x, R x (f x).
Proof.
  intros R [f Hf] Htot.
  assert (H : forall x, exists n, f (x, n) = true).  { intros x. destruct (Htot x) as [y]. exists y. now eapply Hf. }
  eexists (fun x => proj1_sig (constructive_indefinite_ground_description_nat _ _ (H x))).
  intros x. destruct constructive_indefinite_ground_description_nat as [n Hn]; cbn.
  eapply (Hf (x, n)), Hn.
  Unshelve. intros. cbn. destruct f; firstorder congruence.
Qed.

Lemma semi_decidable_AC X (R : X -> nat -> Prop) :
  semi_decidable (uncurry R) ->
  (forall x, exists y, R x y) ->
  exists f : X -> nat, forall x, R x (f x).
Proof.
  intros [g Hg] Htot'. red in Hg. unfold uncurry in *.
  pose (R' x := fun! âŸ¨n,mâŸ© => g (x,n) m = true).
  assert (Htot : forall x, exists n, R' x n). {
    subst R'. intros x. destruct (Htot' x) as (n & [m H] % (Hg (_, _))).
    exists âŸ¨n,mâŸ©. now rewrite embedP.
  }
  assert (Hdec : decidable (uncurry R')). {
    exists  (fun '(x, nm) => let (n, m) := unembed nm in g (x, n) m).
    unfold R'. unfold uncurry. intros (x, nm). destruct (unembed nm) as (n, m).
    destruct g; firstorder congruence.
  }
  eapply (decidable_AC _ _ Hdec) in Htot as [f' Hf'].
  exists (fun x => (fun! âŸ¨n, mâŸ© => n) (f' x)).
  intros x. subst R'. specialize (Hf' x). cbn in Hf'.
  destruct (unembed (f' x)). eapply (Hg (_, _)). eauto.
Qed.

Lemma sdec_compute_lor {X} {p q : X -> Prop} :
  semi_decidable p -> semi_decidable q -> (forall x, p x \/ q x) -> exists f : X -> bool, forall x, if f x then p x else q x.
Proof.
  intros Hp Hq Hpq.
  edestruct (semi_decidable_AC X (fun x n => match n with 0 => p x | _ => q x end)) as [f Hf].
  - destruct Hp as [f1 H1], Hq as [f2 H2]. 
    exists (fun '(x,n) m => match n with 0 => f1 x m | _ => f2 x m end).
    now intros (x,[]); cbn; rewrite ?H1, ?H2. 
  - intros x. destruct (Hpq x). now exists 0. now exists 1.
  - exists (fun x => match f x with 0 => true | _ => false end). intros x.
    specialize (Hf x). destruct (f x); firstorder.
Qed.


Lemma AUC_to_dec (p : nat -> Prop) :
  AUC_on nat bool -> (forall n, p n \/ ~ p n) -> decidable p.
Proof.
  admit.
Admitted.

(* Markov's principle and Post's theorem *)

Definition MP_semidecidable := forall X (p : X -> Prop), semi_decidable p -> forall x, ~~ p x -> p x.
Definition Post_logical := forall X (p : X -> Prop), semi_decidable p -> semi_decidable (fun x => ~ p x) -> forall x, p x \/ ~ p x.
Definition Post := forall X (p : X -> Prop), semi_decidable p -> semi_decidable (fun x => ~ p x) -> decidable p.

Lemma MP_to_MP_semidecidable :
  MP -> MP_semidecidable.
Proof.
Admitted.

Lemma semi_decidable_or {X} {p q : X -> Prop} :
  semi_decidable p -> semi_decidable q -> semi_decidable (fun x => p x \/ q x).
Proof. Admitted.

Lemma MP_semidecidable_to_Post_logical :
  MP_semidecidable -> Post_logical.
Proof. Admitted.

Lemma Post_logical_to_Post :
  Post_logical -> Post.
Proof. Admitted.

Lemma Post_nempty_to_MP {X} (x0 : X) :
  (forall (p : X -> Prop), semi_decidable p -> semi_decidable (fun x => ~ p x) -> decidable p) -> MP.
Proof. Admitted.

Lemma Post_to_MP :
  Post -> MP.
Proof. Admitted.