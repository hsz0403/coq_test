From Huffman Require Export AuxLib.
From Huffman Require Export OrderedCover.
From Huffman Require Export WeightTree.
Require Import ArithRing.
From Huffman Require Export Ordered.
From Huffman Require Export Prod2List.
Section HeightPred.
Variable A : Type.
Variable f : A -> nat.
Variable eqA_dec : forall a b : A, {a = b} + {a <> b}.
Inductive height_pred : nat -> list nat -> list (btree A) -> btree A -> Prop := | height_pred_nil : forall (n : nat) (t : btree A), height_pred n (n :: []) (t :: []) t | height_pred_node : forall (n : nat) (ln1 ln2 : list nat) (t1 t2 : btree A) (l1 l2 : list (btree A)), height_pred (S n) ln1 l1 t1 -> height_pred (S n) ln2 l2 t2 -> height_pred n (ln1 ++ ln2) (l1 ++ l2) (node t1 t2).
Hint Resolve height_pred_nil height_pred_node : core.
End HeightPred.
Arguments height_pred [A].
Hint Resolve height_pred_nil height_pred_node : core.

Theorem weight_tree_compute : forall (m : list A) t, distinct_leaves t -> (forall a : A, f a = number_of_occurrences eqA_dec a m) -> length (encode eqA_dec (compute_code t) m) = weight_tree f t.
Proof using.
intros m t H0 H.
rewrite frequency_length; auto.
apply trans_equal with (0 * sum_leaves f t + weight_tree f t); auto.
rewrite height_pred_weight with (1 := height_pred_compute_code 0 t).
unfold prod2list in |- *.
rewrite fold_left_eta with (f := fun (a : nat) (b : A * list bool) => a + number_of_occurrences eqA_dec (fst b) m * length (snd b)) (f1 := fun (a : nat) (b : A * list bool) => a + (fun b => f (fst b) * length (snd b)) b); auto.
rewrite <- (fold_left_map _ _ (fun a b : nat => a + b) _ 0 (compute_code t) (fun b : A * list bool => f (fst b) * length (snd b))) .
rewrite fold_left_eta with (f := fun a b : nat => a + b) (f1 := plus); auto.
apply f_equal3 with (f := fold_left (A:=nat) (B:=nat)); auto.
elim (compute_code t); simpl in |- *; auto.
intros a l H1; apply f_equal2 with (f := cons (A:=nat)); auto with arith.
ring.
apply btree_unique_prefix2; auto.
