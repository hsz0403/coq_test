From Huffman Require Export Cover.
From Huffman Require Export WeightTree.
Section CoverMin.
Variable A : Type.
Variable f : A -> nat.
Definition cover_min (l : list (btree A)) (t1 : btree A) : Prop := cover l t1 /\ (forall t2 : btree A, cover l t2 -> weight_tree f t1 <= weight_tree f t2).
Hint Resolve cover_min_one : core.
End CoverMin.
Hint Resolve cover_min_one : core.

Theorem cover_min_permutation : forall (t : btree A) (l1 l2 : list (btree A)), cover_min l1 t -> permutation l1 l2 -> cover_min l2 t.
Proof using.
intros t l1 l2 H H0; split.
apply cover_permutation with (2 := H0); auto.
inversion H; auto.
intros t2 H1.
assert (cover l1 t2).
inversion H; auto.
apply cover_permutation with (2 := permutation_sym _ _ _ H0); auto.
inversion H; auto.
