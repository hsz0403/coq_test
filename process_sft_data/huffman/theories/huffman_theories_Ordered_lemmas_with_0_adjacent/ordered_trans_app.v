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

Theorem ordered_trans_app : forall (a b : A) (l1 l2 : list A), ordered (l1 ++ l2) -> In a l1 -> In b l2 -> order a b.
Proof using A order order_trans.
intros a b l1 l2; generalize a b; elim l1; simpl in |- *; clear l1 a b.
intros a b H H1; case H1.
intros c l H a b H0 [H1| H1] H2.
rewrite <- H1; apply ordered_trans with (1 := H0); auto with datatypes.
apply H; auto.
apply ordered_inv with (1 := H0); auto.
