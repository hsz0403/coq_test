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

Lemma height_pred_disj_larger2_aux : forall (n : nat) (ln : list nat) (t : btree A) (l : list (btree A)), height_pred n ln l t -> forall ln1 ln2 a, ln = ln1 ++ a :: ln2 -> (exists n1, In n1 ln1 /\ a <= n1) \/ (exists n1, In n1 ln2 /\ a <= n1) \/ ln = n :: [] /\ l = t :: [].
Proof using.
intros n ln t l H; elim H; clear H n ln t l.
intros n t l ln1 ln2 a; case ln1; simpl in |- *; auto.
intros n ln1 ln2 t1 t2 l1 l2 H H0 H1 H2 ln0 ln3 a H3.
case app_inv_app with (1 := H3).
intros (ln4, H4); auto.
cut (ln3 = ln4 ++ ln2); [ intros E1 | apply app_inv_head with (l := ln0 ++ a :: []); repeat rewrite app_ass; simpl in |- *; rewrite <- H3; rewrite H4; rewrite app_ass; auto ].
case H0 with (1 := H4); auto; intros [(n1, (HH1, HH2))| (HH1, HH2)]; auto; clear H0 H2.
right; left; exists n1; split; auto; rewrite E1; auto with datatypes.
cut (ln0 = [] /\ ln4 = [] /\ a = S n); [ intros (HH3, (HH4, HH5)) | generalize HH1; rewrite H4; case ln0; simpl in |- *; [ case ln4; try (intros; discriminate); (intros HH6; injection HH6; auto) | intros n0 l; case l; simpl in |- *; intros; discriminate ] ].
case height_pred_larger_ex with (1 := H1); auto.
intros n1; rewrite <- HH5; intros (HM1, HM2).
right; left; exists n1; split; auto; rewrite E1; auto with datatypes.
intros (ln4, H4); auto.
cut (ln0 = ln1 ++ ln4); [ intros E1 | apply app_inv_tail with (l := a :: ln3); rewrite <- H3; rewrite H4; rewrite app_ass; auto ].
case H2 with (1 := H4); auto; clear H0 H2.
intros (n1, (HH1, HH2)); left; exists n1; split; auto; rewrite E1; auto with datatypes.
intros [HH1| (HH1, HH2)]; auto.
cut (ln3 = [] /\ ln4 = [] /\ a = S n); [ intros (HH3, (HH4, HH5)) | generalize HH1; rewrite H4; case ln4; simpl in |- *; [ case ln3; try (intros; discriminate); (intros HH6; injection HH6; auto) | intros n0 l; case l; simpl in |- *; intros; discriminate ] ].
case height_pred_larger_ex with (1 := H); auto.
intros n1; rewrite <- HH5; intros (HM1, HM2).
left; exists n1; split; auto; rewrite E1; auto with datatypes.
