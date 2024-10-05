From Huffman Require Import HeightPred.
Section SubstPred.
Variable A : Type.
Inductive subst_pred : list (btree A) -> list (btree A) -> btree A -> btree A -> Prop := | subst_pred_id : forall (t1 t2 : btree A) (l1 l2 : list (btree A)), subst_pred (t1 :: []) (t2 :: []) t1 t2 | subst_pred_node : forall (t1 t2 t3 t4 : btree A) (l1 l2 l3 l4 l5 l6 : list (btree A)), subst_pred l1 l2 t1 t2 -> subst_pred l3 l4 t3 t4 -> subst_pred (l1 ++ l3) (l2 ++ l4) (node t1 t3) (node t2 t4).
Hint Resolve subst_pred_id subst_pred_node : core.
End SubstPred.
Arguments subst_pred [A].
Hint Resolve subst_pred_id : core.

Theorem height_pred_subst_pred : forall (n : nat) (ln : list nat) (t1 : btree A) (l1 l2 : list (btree A)), height_pred n ln l1 t1 -> length l1 = length l2 -> exists t2 : btree A, height_pred n ln l2 t2 /\ subst_pred l1 l2 t1 t2.
Proof using.
intros n ln t1 l1 l2 H; generalize l2; elim H; clear H n ln t1 l1 l2; auto.
intros n t l2; case l2.
simpl in |- *; intros; discriminate.
intros b l0; case l0; intros; try discriminate; exists b; auto.
intros n ln1 ln2 t1 t2 l1 l2 H H0 H1 H2 l0 H3.
case (H0 (firstn (length l1) l0)); auto.
rewrite firstn_le_length_eq; auto; (rewrite <- H3; rewrite app_length; auto with arith).
intros t4 (HH1, HH2).
case (H2 (skipn (length l1) l0)); auto.
rewrite length_skipn; auto; (rewrite <- H3; rewrite app_length; rewrite minus_plus; auto with arith).
intros t5 (HH3, HH4).
exists (node t4 t5); rewrite <- (firstn_skipn (length l1) l0); auto.
