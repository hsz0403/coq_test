From Huffman Require Export WeightTree.
Require Import ArithRing.
From Huffman Require Export Ordered.
Section Prod2List.
Variable A : Type.
Variable f : A -> nat.
Definition prod2list l1 l2 := fold_left plus (map2 (fun a b => a * sum_leaves f b + weight_tree f b) l1 l2) 0.
End Prod2List.
Arguments prod2list [A].

Theorem prod2list_eq : forall a b c l1 l2 l3 l4 l5 l6, length l1 = length l4 -> length l2 = length l5 -> length l3 = length l6 -> prod2list (l1 ++ a :: l2 ++ a :: l3) (l4 ++ b :: l5 ++ c :: l6) = prod2list (l1 ++ a :: l2 ++ a :: l3) (l4 ++ c :: l5 ++ b :: l6).
Proof using.
intros a b c l1 l2 l3 l4 l5 l6 H H0 H1; change (prod2list (l1 ++ (a :: []) ++ l2 ++ (a :: []) ++ l3) (l4 ++ (b :: []) ++ l5 ++ (c :: []) ++ l6) = prod2list (l1 ++ (a :: []) ++ l2 ++ (a :: []) ++ l3) (l4 ++ (c :: []) ++ l5 ++ (b :: []) ++ l6)) in |- *.
repeat rewrite prod2list_app; auto with arith.
ring.
