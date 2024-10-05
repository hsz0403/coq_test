From Huffman Require Export WeightTree.
From Huffman Require Export Ordered.
From Huffman Require Export SameSumLeaves.
Section OneStep.
Variable A : Type.
Variable f : A -> nat.
Definition one_step (l1 l2 : list (btree A)) : Prop := exists l3 : list (btree A), (exists t1 : btree A, (exists t2 : btree A, ordered (sum_order f) (t1 :: t2 :: l3) /\ permutation l1 (t1 :: t2 :: l3) /\ permutation l2 (node t1 t2 :: l3))).
End OneStep.
Arguments one_step [A].

Theorem one_step_comp : forall l1 l2 l3 l4 : list (btree A), weight_tree_list f l1 = weight_tree_list f l2 -> same_sum_leaves f l1 l2 -> one_step l1 l3 -> one_step l2 l4 -> weight_tree_list f l3 = weight_tree_list f l4 /\ same_sum_leaves f l3 l4.
Proof using.
intros l1 l2 l3 l4 H1 (l5, (l6, (H2, (H3, H4)))) (l7, (t1, (t2, (H5, (H6, H7))))) (l8, (t3, (t4, (H8, (H9, H10))))).
cut (map (sum_leaves f) (t1 :: t2 :: l7) = map (sum_leaves f) (t3 :: t4 :: l8)).
intros H11.
split.
rewrite weight_tree_list_permutation with (1 := H7).
rewrite weight_tree_list_permutation with (1 := H10).
repeat rewrite weight_tree_list_node.
apply f_equal2 with (f := plus).
injection H11; intros H12 H13 H14; auto.
rewrite weight_tree_list_permutation with (1 := permutation_sym _ _ _ H6).
rewrite weight_tree_list_permutation with (1 := permutation_sym _ _ _ H9); auto.
red in |- *; exists (node t1 t2 :: l7); exists (node t3 t4 :: l8); repeat (split; auto).
simpl in |- *.
simpl in H11; injection H11; auto.
intros; apply f_equal2 with (f := cons (A:=nat)); auto.
apply ordered_perm_antisym_eq with (order := le).
exact le_trans.
exact le_antisym.
apply permutation_trans with (map (sum_leaves f) l1).
generalize (permutation_map _ _ (sum_leaves f) _ _ (permutation_sym _ _ _ H6)); auto.
apply permutation_trans with (map (sum_leaves f) l5).
generalize (permutation_map _ _ (sum_leaves f) _ _ H2); auto.
rewrite H4.
apply permutation_trans with (map (sum_leaves f) l2).
generalize (permutation_map _ _ (sum_leaves f) _ _ (permutation_sym _ _ _ H3)); auto.
generalize (permutation_map _ _ (sum_leaves f) _ _ H9); auto.
change (ordered le (map (sum_leaves f) (t1 :: t2 :: l7))) in |- *.
apply ordered_map_inv; auto.
change (ordered le (map (sum_leaves f) (t3 :: t4 :: l8))) in |- *.
apply ordered_map_inv; auto.
