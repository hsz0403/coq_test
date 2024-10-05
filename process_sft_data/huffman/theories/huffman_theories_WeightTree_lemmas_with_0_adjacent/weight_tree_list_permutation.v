From Huffman Require Export BTree.
From Huffman Require Export Ordered.
Require Import ArithRing.
Section WeightTree.
Variable A : Type.
Variable f : A -> nat.
Fixpoint sum_leaves (t : btree A) : nat := match t with | leaf n => f n | node t1 t2 => sum_leaves t1 + sum_leaves t2 end.
Definition sum_order x y := sum_leaves x <= sum_leaves y.
Definition le_sum x y := le_bool (sum_leaves x) (sum_leaves y).
Fixpoint weight_tree (t : btree A) : nat := match t with | leaf n => 0 | node t1 t2 => sum_leaves t1 + weight_tree t1 + (sum_leaves t2 + weight_tree t2) end.
Definition weight_tree_list : list (btree A) -> nat := fold_right (fun x : btree A => plus (weight_tree x)) 0.
End WeightTree.
Arguments sum_leaves [A].
Arguments sum_order [A].
Arguments le_sum [A].
Arguments weight_tree [A].
Arguments weight_tree_list [A].

Theorem weight_tree_list_permutation : forall l1 l2 : list (btree A), permutation l1 l2 -> weight_tree_list l1 = weight_tree_list l2.
Proof using.
intros l1 l2 H; elim H; auto.
simpl in |- *; auto; intros; ring.
simpl in |- *; auto; intros; ring.
intros l0 l3 l4 H0 H1 H2 H3; apply trans_equal with (1 := H1); auto.
