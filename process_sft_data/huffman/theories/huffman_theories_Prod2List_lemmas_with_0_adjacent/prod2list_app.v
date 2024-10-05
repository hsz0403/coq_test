From Huffman Require Export WeightTree.
Require Import ArithRing.
From Huffman Require Export Ordered.
Section Prod2List.
Variable A : Type.
Variable f : A -> nat.
Definition prod2list l1 l2 := fold_left plus (map2 (fun a b => a * sum_leaves f b + weight_tree f b) l1 l2) 0.
End Prod2List.
Arguments prod2list [A].

Theorem prod2list_app : forall l1 l2 l3 l4, length l1 = length l2 -> prod2list (l1 ++ l3) (l2 ++ l4) = prod2list l1 l2 + prod2list l3 l4.
Proof using.
intros l1 l2 l3 l4 H; unfold prod2list in |- *.
rewrite map2_app; auto.
rewrite fold_left_app.
rewrite plus_comm.
apply sym_equal.
repeat rewrite fold_left_eta with (f := plus) (f1 := fun a b : nat => a + (fun x => x) b); auto.
apply sym_equal; rewrite <- fold_plus_split with (f := fun x : nat => x); auto.
apply plus_comm.
