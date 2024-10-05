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

Theorem height_pred_shrink : forall (n a b : nat) (ln1 ln2 : list nat) (t t1 t2 : btree A) (l1 l2 : list (btree A)), height_pred n (ln1 ++ a :: b :: ln2) (l1 ++ t1 :: t2 :: l2) t -> (forall n1 : nat, In n1 ln1 -> n1 < a) -> (forall n1 : nat, In n1 (b :: ln2) -> n1 <= a) -> length ln1 = length l1 -> height_pred n (ln1 ++ pred a :: ln2) (l1 ++ node t1 t2 :: l2) t.
Proof using.
intros n a b ln1 ln2 t t1 t2 l1 l2 H H0 H1 H2; apply height_pred_shrink_aux with (1 := H) (b := b); auto.
