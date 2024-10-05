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

Theorem ordered_inv : forall (a : A) (l : list A), ordered (a :: l) -> ordered l.
Proof using.
intros a l H; inversion H; auto.
