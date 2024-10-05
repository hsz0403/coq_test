From Huffman Require Export WeightTree.
Require Import ArithRing.
From Huffman Require Export Ordered.
Section Prod2List.
Variable A : Type.
Variable f : A -> nat.
Definition prod2list l1 l2 := fold_left plus (map2 (fun a b => a * sum_leaves f b + weight_tree f b) l1 l2) 0.
End Prod2List.
Arguments prod2list [A].

Theorem prod2list_reorder2 : forall a b c b1 c1 l1 l2 l3 l4 l5, length l1 = length l3 -> length l2 = length l4 -> (forall b, In b l1 -> b <= a) -> (forall b, In b l2 -> b <= a) -> permutation (l3 ++ b :: c :: l4) (b1 :: c1 :: l5) -> ordered (sum_order f) (b1 :: c1 :: l5) -> exists l6, (exists l7, length l1 = length l6 /\ length l2 = length l7 /\ permutation (b1 :: c1 :: l5) (l6 ++ b1 :: c1 :: l7) /\ prod2list (l1 ++ a :: a :: l2) (l6 ++ b1 :: c1 :: l7) <= prod2list (l1 ++ a :: a :: l2) (l3 ++ b :: c :: l4)).
Proof using.
intros a b c b1 c1 l1 l2 l3 l4 l5 H H0 H1 H2 H3 H4.
case (prod2list_reorder a b b1 l1 (a :: l2) l3 (c :: l4) (c1 :: l5)); simpl in |- *; auto.
intros b0 [H5| H5]; auto.
rewrite H5; auto.
intros l6 (l7, (HH1, (HH2, (HH3, HH4)))).
generalize HH2 HH3 HH4; case l7; clear HH2 HH3 HH4 l7.
intros; discriminate.
intros c2 l7 HH2 HH3 HH4.
case (prod2list_reorder a c2 c1 l1 l2 l6 l7 l5); simpl in |- *; auto.
apply permutation_inv with (a := b1); auto.
apply permutation_sym; apply permutation_trans with (1 := HH3).
change (permutation (l6 ++ (b1 :: []) ++ c2 :: l7) (((b1 :: []) ++ l6) ++ c2 :: l7)) in |- *.
repeat rewrite <- app_ass.
apply permutation_app_comp; auto.
apply ordered_inv with (1 := H4); auto.
intros l8 (l9, (HH5, (HH6, (HH7, HH8)))).
exists l8; exists l9; repeat (split; auto).
apply permutation_trans with ((b1 :: c1 :: l9) ++ l8); auto.
simpl in |- *; apply permutation_skip; auto.
apply permutation_trans with (1 := HH7).
apply permutation_trans with ((c1 :: l9) ++ l8); auto.
apply le_trans with (2 := HH4).
change (prod2list (l1 ++ (a :: []) ++ a :: l2) (l8 ++ (b1 :: []) ++ c1 :: l9) <= prod2list (l1 ++ (a :: []) ++ a :: l2) (l6 ++ (b1 :: []) ++ c2 :: l7)) in |- *.
generalize HH8; repeat rewrite prod2list_app; auto with arith.
intros HH9.
repeat rewrite plus_assoc.
repeat rewrite (fun x => plus_comm (prod2list l1 x)).
repeat rewrite plus_assoc_reverse; auto with arith.
