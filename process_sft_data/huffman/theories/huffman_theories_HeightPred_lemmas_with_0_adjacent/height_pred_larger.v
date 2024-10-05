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

Theorem height_pred_larger : forall (n n1 : nat) (ln : list nat) (t : btree A) (l : list (btree A)), height_pred n ln l t -> In n1 ln -> n <= n1.
Proof using.
intros n n1 ln t l H; generalize n1; elim H; clear H n ln t l n1; auto with arith.
intros n t n1 [H2| H2]; [ rewrite H2 | case H2 ]; auto.
intros n ln1 ln2 t1 t2 l1 l2 H H0 H1 H2 n1 H3; apply le_trans with (S n); auto with arith.
case in_app_or with (1 := H3); auto.
