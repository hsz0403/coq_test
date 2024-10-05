From Huffman Require Export Cover.
Section OrderedCover.
Variable A : Type.
Inductive ordered_cover : list (btree A) -> btree A -> Prop := | ordered_cover_one : forall (t : btree A) (l : list (btree A)), ordered_cover (t :: []) t | ordered_cover_node : forall (t1 t2 : btree A) (l1 l2 l3 : list (btree A)), ordered_cover l1 t1 -> ordered_cover l2 t2 -> ordered_cover (l1 ++ l2) (node t1 t2).
Hint Resolve ordered_cover_one ordered_cover_node : core.
End OrderedCover.
Arguments ordered_cover [A].
Hint Resolve ordered_cover_one ordered_cover_node : core.

Theorem cover_ordered_cover : forall (l1 : list (btree A)) (t : btree A), cover l1 t -> exists l2, permutation l1 l2 /\ ordered_cover l2 t.
Proof using.
intros l1; elim l1 using list_length_ind.
intros l0 H t; case t.
intros a H1; rewrite cover_inv_leaf with (1 := H1).
exists (leaf a :: []); auto.
intros t1 t2 H1; case cover_inv_app with (1 := H1).
intros H2; exists l0; split; auto; rewrite H2; auto.
intros (l2, (l3, ((HH1, HH2), HH3))).
case H with (2 := HH1); auto.
rewrite permutation_length with (1 := HH3).
generalize HH2; rewrite app_length; case l3; simpl in |- *; auto with arith.
intros HH4; case cover_not_nil with (1 := HH4); auto.
intros; rewrite plus_comm; simpl in |- *; auto with arith.
intros l4 (HP1, HP2).
case H with (2 := HH2); auto.
rewrite permutation_length with (1 := HH3).
generalize HH1; rewrite app_length; case l2; simpl in |- *; auto with arith.
intros HH4; case cover_not_nil with (1 := HH4); auto.
intros l5 (HP3, HP4).
exists (l4 ++ l5); split; auto.
apply permutation_trans with (1 := HH3); auto.
