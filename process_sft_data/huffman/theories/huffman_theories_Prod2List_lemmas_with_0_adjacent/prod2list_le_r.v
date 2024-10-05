From Huffman Require Export WeightTree.
Require Import ArithRing.
From Huffman Require Export Ordered.
Section Prod2List.
Variable A : Type.
Variable f : A -> nat.
Definition prod2list l1 l2 := fold_left plus (map2 (fun a b => a * sum_leaves f b + weight_tree f b) l1 l2) 0.
End Prod2List.
Arguments prod2list [A].

Theorem prod2list_le_r : forall a b c d l1 l2 l3 l4 l5 l6, length l1 = length l4 -> length l2 = length l5 -> length l3 = length l6 -> sum_leaves f d <= sum_leaves f c -> b <= a -> prod2list (l1 ++ a :: l2 ++ b :: l3) (l4 ++ d :: l5 ++ c :: l6) <= prod2list (l1 ++ a :: l2 ++ b :: l3) (l4 ++ c :: l5 ++ d :: l6).
Proof using.
intros a b c d l1 l2 l3 l4 l5 l6 H H0 H1 H2 H3; change (prod2list (l1 ++ (a :: []) ++ l2 ++ (b :: []) ++ l3) (l4 ++ (d :: []) ++ l5 ++ (c :: []) ++ l6) <= prod2list (l1 ++ (a :: []) ++ l2 ++ (b :: []) ++ l3) (l4 ++ (c :: []) ++ l5 ++ (d :: []) ++ l6)) in |- *.
repeat rewrite prod2list_app; auto.
apply plus_le_compat; auto with arith.
repeat rewrite plus_assoc; apply plus_le_compat; auto.
repeat rewrite (fun x y z => plus_comm (prod2list (x :: y) z)).
repeat rewrite plus_assoc_reverse; apply plus_le_compat; auto.
unfold prod2list in |- *; simpl in |- *.
rewrite le_plus_minus with (1 := H3); auto.
rewrite le_plus_minus with (1 := H2); auto.
replace ((b + (a - b)) * (sum_leaves f d + (sum_leaves f c - sum_leaves f d)) + weight_tree f c + (b * sum_leaves f d + weight_tree f d)) with ((b + (a - b)) * sum_leaves f d + weight_tree f d + ((b + (a - b)) * (sum_leaves f c - sum_leaves f d) + b * sum_leaves f d + weight_tree f c)); [ idtac | ring ].
apply plus_le_compat; auto with arith.
apply plus_le_compat; auto with arith.
repeat rewrite mult_plus_distr_l || rewrite mult_plus_distr_r; auto with arith.
replace (b * sum_leaves f d + b * (sum_leaves f c - sum_leaves f d)) with (b * (sum_leaves f c - sum_leaves f d) + 0 + b * sum_leaves f d); [ auto with arith | ring ].
