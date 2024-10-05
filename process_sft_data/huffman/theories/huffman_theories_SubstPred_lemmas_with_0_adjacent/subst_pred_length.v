From Huffman Require Import HeightPred.
Section SubstPred.
Variable A : Type.
Inductive subst_pred : list (btree A) -> list (btree A) -> btree A -> btree A -> Prop := | subst_pred_id : forall (t1 t2 : btree A) (l1 l2 : list (btree A)), subst_pred (t1 :: []) (t2 :: []) t1 t2 | subst_pred_node : forall (t1 t2 t3 t4 : btree A) (l1 l2 l3 l4 l5 l6 : list (btree A)), subst_pred l1 l2 t1 t2 -> subst_pred l3 l4 t3 t4 -> subst_pred (l1 ++ l3) (l2 ++ l4) (node t1 t3) (node t2 t4).
Hint Resolve subst_pred_id subst_pred_node : core.
End SubstPred.
Arguments subst_pred [A].
Hint Resolve subst_pred_id : core.

Theorem subst_pred_length : forall (t1 t2 : btree A) (l1 l2 : list (btree A)), subst_pred l1 l2 t1 t2 -> length l1 = length l2.
Proof using.
intros t1 t2 l1 l2 H; elim H; auto.
intros t0 t3 t4 t5 l0 l3 l4 l5 l6 l7 H0 H1 H2 H3; repeat rewrite app_length; auto.
