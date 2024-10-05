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

Theorem ordered_sum_leaves_eq : forall (A : Type) (f : A -> nat) (l1 l2 : list (btree A)), permutation l1 l2 -> ordered (sum_order f) l1 -> ordered (sum_order f) l2 -> map (sum_leaves f) l1 = map (sum_leaves f) l2.
Proof using.
intros A f l1 l2 H H0 H1.
apply ordered_perm_antisym_eq with (order := le).
exact le_trans.
exact le_antisym.
apply permutation_map; auto.
apply ordered_map_inv; auto.
apply ordered_map_inv; auto.
