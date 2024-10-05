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

Theorem ordered_cover_height_pred : forall (n : nat) (t : btree A) (l : list (btree A)), ordered_cover l t -> exists ln : list nat, height_pred n ln l t.
Proof using.
intros n t l H; generalize n; elim H; clear n t l H.
intros t l n; exists (n :: []); auto.
intros t1 t2 l1 l2 l3 H H0 H1 H2 n.
case (H0 (S n)); intros ln1 HH1.
case (H2 (S n)); intros ln2 HH2.
exists (ln1 ++ ln2); auto.
