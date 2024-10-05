From Huffman Require Export WeightTree.
From Huffman Require Export Ordered.
From Huffman Require Export SameSumLeaves.
Section OneStep.
Variable A : Type.
Variable f : A -> nat.
Definition one_step (l1 l2 : list (btree A)) : Prop := exists l3 : list (btree A), (exists t1 : btree A, (exists t2 : btree A, ordered (sum_order f) (t1 :: t2 :: l3) /\ permutation l1 (t1 :: t2 :: l3) /\ permutation l2 (node t1 t2 :: l3))).
End OneStep.
Arguments one_step [A].

Theorem one_step_weight_tree_list : forall l1 l2 l3 : list (btree A), one_step l1 l2 -> one_step l1 l3 -> weight_tree_list f l2 = weight_tree_list f l3.
Proof using.
intros l1 l2 l3 (l4, (t1, (t2, (H1, (H2, H3))))) (l5, (t3, (t4, (H4, (H5, H6))))).
rewrite weight_tree_list_permutation with (1 := H3).
rewrite weight_tree_list_permutation with (1 := H6).
repeat rewrite weight_tree_list_node.
apply f_equal2 with (f := plus).
cut (map (sum_leaves f) (t1 :: t2 :: l4) = map (sum_leaves f) (t3 :: t4 :: l5)).
simpl in |- *; intros H7; injection H7.
intros H8 H9 H10; repeat apply f_equal2 with (f := plus); auto.
apply ordered_sum_leaves_eq; auto.
apply permutation_trans with (2 := H5); auto.
apply permutation_sym; auto.
rewrite <- weight_tree_list_permutation with (1 := H2).
apply weight_tree_list_permutation; auto.
