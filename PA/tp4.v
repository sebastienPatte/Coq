Require Import List.
Import ListNotations.

Lemma cons_inj {A} (x1 x2 : A) (l1 l2 : list A) : x1::l1 = x2::l2 -> x1=x2 /\ l1=l2.
Proof.
  intro.
  split.
  - eapply f_equal with (f:= fun l => match l with |[] => x1 |x::l'=> x end) in H.
    assumption.
  - eapply f_equal with (f:= fun l => match l with |[] => l1 |x::l'=> l' end) in H.
    assumption.
Qed.

Lemma discr_nil_cons {A} (x:A) (l:list A) : nil <> x::l.
Proof.
  unfold not.
  intro.
  eapply f_equal with (f:= fun x => match x with nil => True |_ => False end) in H.
  rewrite <- H.
  trivial.
Qed.

Fail Inductive lambda := Lam (_:lambda->lambda).

Parameter lambda : Type.
Parameter Lam : (lambda->lambda) -> lambda.

Parameter match_lambda : forall P:lambda -> Type, (forall (l:lambda->lambda), P (Lam l) ) -> forall l, P l.

Parameter lambda_eq : forall P H f, match_lambda P H (Lam f) = H f.

Definition app (l1 l2 : lambda) := 
  match_lambda (fun _ => lambda) (fun f => f l2) l1
.

Lemma app_red : forall(f:lambda -> lambda) (x:lambda), app (Lam f) x = f x.
Proof.
  intros.
  unfold app.
  rewrite lambda_eq.
  reflexivity.
Qed. 


Definition Y := Lam (fun f => 
  app 
    (Lam (fun x => app f (app x x))) 
    (Lam (fun x => app f (app x x))) 
).

Lemma fixpt : forall (f:lambda -> lambda), exists t, f t = t.
Proof.
  intros.
  exists (app Y (Lam f)).
  unfold Y at 1.
  
  
  rewrite app_red.
  rewrite app_red.
  rewrite app_red.
  unfold Y.
  rewrite app_red at 2.
  rewrite a pp_red.
  rewrite app_red.
  
  
  
  
  

