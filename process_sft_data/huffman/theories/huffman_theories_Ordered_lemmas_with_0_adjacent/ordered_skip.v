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

Theorem ordered_skip : forall (a b : A) (l : list A), ordered (a :: b :: l) -> ordered (a :: l).
Proof using A order order_trans.
intros a b l; case l; clear l; auto.
intros c l H; apply ordered_cons.
apply order_trans with (b := b); auto.
apply ordered_inv_order with (1 := H).
apply ordered_inv_order with (1 := ordered_inv _ _ H).
apply ordered_inv with (1 := ordered_inv _ _ H).
