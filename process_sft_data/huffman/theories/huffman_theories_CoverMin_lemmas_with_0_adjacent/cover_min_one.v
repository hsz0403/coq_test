From Huffman Require Export Cover.
From Huffman Require Export WeightTree.
Section CoverMin.
Variable A : Type.
Variable f : A -> nat.
Definition cover_min (l : list (btree A)) (t1 : btree A) : Prop := cover l t1 /\ (forall t2 : btree A, cover l t2 -> weight_tree f t1 <= weight_tree f t2).
Hint Resolve cover_min_one : core.
End CoverMin.
Hint Resolve cover_min_one : core.

Theorem cover_min_one : forall t : btree A, cover_min (t :: []) t.
Proof using.
intros t; split; auto.
intros t2 H; inversion H; auto.
generalize (permutation_length _ _ _ H0); simpl in |- *; intros; discriminate.
