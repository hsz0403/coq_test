From Huffman Require Export WeightTree.
Require Import ArithRing.
From Huffman Require Export Ordered.
Section Prod2List.
Variable A : Type.
Variable f : A -> nat.
Definition prod2list l1 l2 := fold_left plus (map2 (fun a b => a * sum_leaves f b + weight_tree f b) l1 l2) 0.
End Prod2List.
Arguments prod2list [A].

Theorem prod2list_reorder : forall a b b1 l1 l2 l3 l4 l5, length l1 = length l3 -> length l2 = length l4 -> (forall b, In b l1 -> b <= a) -> (forall b, In b l2 -> b <= a) -> permutation (l3 ++ b :: l4) (b1 :: l5) -> ordered (sum_order f) (b1 :: l5) -> exists l6, (exists l7, length l1 = length l6 /\ length l2 = length l7 /\ permutation (b1 :: l5) (l6 ++ b1 :: l7) /\ prod2list (l1 ++ a :: l2) (l6 ++ b1 :: l7) <= prod2list (l1 ++ a :: l2) (l3 ++ b :: l4)).
Proof using.
intros a b b1 l1 l2 l3 l4 l5 H H0 H1 H2 H3 H4.
cut (In b (b1 :: l5)); [ simpl in |- *; intros [HH0| HH0] | apply permutation_in with (1 := H3); auto with datatypes ].
exists l3; exists l4; repeat (split; auto).
pattern b1 at 2 in |- *; rewrite HH0; apply permutation_sym; auto.
rewrite HH0; auto.
cut (In b1 (l3 ++ b :: l4)); [ intros HH1 | apply permutation_in with (1 := permutation_sym _ _ _ H3); auto with datatypes ].
case in_app_or with (1 := HH1); intros HH2.
case in_ex_app with (1 := HH2).
intros l6 (l7, HH3); exists (l6 ++ b :: l7); exists l4; repeat (split; auto).
apply trans_equal with (1 := H).
rewrite HH3; repeat rewrite app_length; simpl in |- *; auto with arith.
apply permutation_sym; apply permutation_trans with (2 := H3); auto.
rewrite HH3.
repeat rewrite app_ass.
simpl in |- *; apply permutation_transposition.
rewrite HH3; auto.
repeat rewrite app_ass.
case (same_length_ex _ _ b1 l6 l7 l1); auto.
rewrite <- HH3; auto.
intros l8 (l9, (b2, (HH4, (HH5, HH6)))).
rewrite HH6.
repeat rewrite app_ass; simpl in |- *.
apply prod2list_le_l; auto.
change (sum_order f b1 b) in |- *.
apply ordered_trans with (2 := H4); auto.
unfold sum_order in |- *; intros a0 b0 c H5 H6; apply le_trans with (1 := H5); auto.
apply H1; rewrite HH6; auto with datatypes.
simpl in HH2; case HH2; intros HH3.
exists l3; exists l4; repeat (split; auto); try (rewrite <- HH3; auto; fail).
pattern b1 at 2 in |- *; rewrite <- HH3; apply permutation_sym; auto.
case in_ex_app with (1 := HH3).
intros l6 (l7, HH4); exists l3; exists (l6 ++ b :: l7); repeat (split; auto).
apply trans_equal with (1 := H0).
rewrite HH4; repeat rewrite app_length; simpl in |- *; auto with arith.
apply permutation_sym; apply permutation_trans with (2 := H3); auto.
rewrite HH4.
simpl in |- *; apply permutation_transposition.
rewrite HH4; auto.
case (same_length_ex _ _ b1 l6 l7 l2); auto.
rewrite <- HH4; auto.
intros l8 (l9, (b2, (HH5, (HH6, HH7)))).
rewrite HH7.
apply prod2list_le_r; auto.
change (sum_order f b1 b) in |- *.
apply ordered_trans with (2 := H4); auto.
unfold sum_order in |- *; intros a0 b0 c H5 H6; apply le_trans with (1 := H5); auto.
apply H2; rewrite HH7; auto with datatypes.
