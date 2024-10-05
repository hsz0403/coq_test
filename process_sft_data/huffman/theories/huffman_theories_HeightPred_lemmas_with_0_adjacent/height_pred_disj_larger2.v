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

Theorem height_pred_disj_larger2 : forall (n a : nat) (ln1 ln2 : list nat) (t : btree A) (l : list (btree A)), height_pred n (ln1 ++ a :: ln2) l t -> (exists n1, In n1 ln1 /\ a <= n1) \/ (exists n1, In n1 ln2 /\ a <= n1) \/ (ln1 = [] /\ a = n /\ ln2 = []) /\ l = t :: [].
Proof using.
intros n a ln1 ln2 t l H; case height_pred_disj_larger2_aux with (a := a) (ln1 := ln1) (ln2 := ln2) (1 := H); auto.
intros [H1| (H1, H2)]; auto.
generalize H1 H2; case ln1; simpl in |- *; [ intros H3; injection H3; auto with datatypes | idtac ].
intros H0 H4 H5; repeat right; auto.
intros n0 l0; case l0; simpl in |- *; intros; discriminate.
