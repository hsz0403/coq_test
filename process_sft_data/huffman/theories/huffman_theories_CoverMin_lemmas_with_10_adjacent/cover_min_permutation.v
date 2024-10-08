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
Admitted.

Theorem cover_min_ex : forall l : list (btree A), l <> [] -> exists t : btree A, cover_min l t.
Proof using.
intros l H; generalize (find_min_correct (btree A) (weight_tree f) (all_cover _ l)).
case (find_min (weight_tree f) (all_cover _ l)).
intros p; case p.
intros n b ((H1, H2), H3); exists b; auto.
split; auto.
apply all_cover_cover; auto.
intros t2 H4; apply H3.
apply cover_all_cover; auto.
intros H0.
case (one_cover_ex _ l); auto.
intros x H1; absurd (In x (all_cover A l)).
rewrite H0; simpl in |- *; red in |- *; intros H2; case H2.
Admitted.

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
