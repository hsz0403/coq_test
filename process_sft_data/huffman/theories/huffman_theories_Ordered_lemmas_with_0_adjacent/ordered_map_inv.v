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

Theorem ordered_map_inv : forall (A B : Type) (order : A -> A -> Prop) (g : B -> A) (l : list B), ordered (fun x y => order (g x) (g y)) l -> ordered order (map g l).
Proof using.
intros A B order g l; elim l; simpl in |- *; auto.
intros a1 l1; case l1; simpl in |- *; auto.
intros b l0 H H0; inversion H0; auto.
