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

Theorem weight_tree_list_node : forall (t1 t2 : btree A) (l : list (btree A)), weight_tree_list (node t1 t2 :: l) = sum_leaves t1 + sum_leaves t2 + weight_tree_list (t1 :: t2 :: l).
Proof using.
intros t1 t2 l; simpl in |- *; ring.
