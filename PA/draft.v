tree_rec :
	forall (A : Type) (P : tree A -> Set),
    (forall (a : A) (f : forest A), P (node A a f)) ->
    forall t : tree A, P t

tree_forest_rec :
	forall (A : Type) (P : tree A -> Set) (Q : forest A -> Set),
    (forall (a : A) (f : forest A),
	   Q f ->
	   P (node A a f)) ->
       Q (nil A) ->
       (forall t : tree A,
        P t -> forall f1 : forest A, Q f1 -> Q (next A t f1)) ->
       forall t : tree A, P t

