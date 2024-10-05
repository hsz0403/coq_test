From Huffman Require Export Permutation.
From Huffman Require Export AuxLib.
Section ordered.
Variable A : Type.
Variable order : A -> A -> Prop.
Hypothesis order_trans : forall a b c : A, order a b -> order b c -> order a c.
Inductive ordered : list A -> Prop := | ordered_nil : ordered [] | ordered_one : forall a : A, ordered (a :: []) | ordered_cons : forall (a b : A) (l : list A), order a b -> ordered (b :: l) -> ordered (a :: b :: l).
Hint Constructors ordered : core.
End ordered.
Hint Constructors ordered : core.
Arguments ordered [A].

Theorem ordered_trans : forall (a b : A) (l : list A), ordered (a :: l) -> In b l -> order a b.
Proof using A order order_trans.
intros a b l; generalize a b; elim l; clear l a b.
intros a b H H2; inversion H2.
simpl in |- *; intros c l H a b H0 [H1| H1].
rewrite <- H1; apply ordered_inv_order with (1 := H0).
apply order_trans with (b := c); auto.
apply ordered_inv_order with (1 := H0).
apply H; auto.
apply ordered_inv with (1 := H0).
