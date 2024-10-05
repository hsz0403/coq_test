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

Lemma height_pred_disj_larger_aux : forall (n : nat) (ln : list nat) (t : btree A) (l : list (btree A)), height_pred n ln l t -> forall ln1 ln2 a, ln = ln1 ++ a :: ln2 -> (forall n1 : nat, In n1 ln1 -> n1 < a) -> (forall n1 : nat, In n1 ln2 -> n1 <= a) -> (exists ln3, ln2 = a :: ln3) \/ ln = n :: [] /\ l = t :: [].
Proof using.
intros n ln t l H; elim H; clear H n ln t l.
intros n t l ln1 ln2 a; case ln1; simpl in |- *; auto.
intros n ln1 ln2 t1 t2 l1 l2 H H0 H1 H2 ln0 ln3 a H3 H4 H5.
case app_inv_app with (1 := H3).
intros (ln4, H7); auto.
cut (ln3 = ln4 ++ ln2); [ intros E1 | apply app_inv_head with (l := ln0 ++ a :: []); repeat rewrite app_ass; simpl in |- *; rewrite <- H3; rewrite H7; rewrite app_ass; auto ].
case H0 with (1 := H7); auto; clear H0 H2.
intros n1 H8; apply H5; rewrite E1; auto with datatypes.
intros (ln5, HH); left; exists (ln5 ++ ln2).
apply trans_equal with (1 := E1); rewrite HH; auto.
intros (HH1, HH2).
cut (ln0 = [] /\ ln4 = [] /\ a = S n); [ intros (HH3, (HH4, HH5)) | generalize HH1; rewrite H7; case ln0; simpl in |- *; [ case ln4; try (intros; discriminate); (intros HH6; injection HH6; auto) | intros n0 l; case l; simpl in |- *; intros; discriminate ] ].
generalize E1 H1; case ln2; simpl in |- *; auto; clear E1 H1.
intros E1 H1; case height_pred_not_nil2 with (1 := H1); auto.
generalize (height_pred_length _ _ _ _ H1); case l2; simpl in |- *; auto; intros; discriminate.
intros n0 ln5 E1 H1; case height_pred_larger_strict with (n1 := n0) (1 := H1); simpl in |- *; auto with datatypes.
intros HH6; contradict HH6; apply le_not_lt; rewrite <- HH5; apply H5; rewrite E1; auto with datatypes.
intros (H8, H9); left; exists []; injection H8.
intros HH7 HH8; rewrite HH5; rewrite <- HH8; rewrite <- HH7; rewrite E1; rewrite HH4; auto.
intros (ln4, H7); auto.
cut (ln0 = ln1 ++ ln4); [ intros E1 | apply app_inv_tail with (l := a :: ln3); rewrite <- H3; rewrite H7; rewrite app_ass; auto ].
case H2 with (1 := H7); auto.
intros n1 H6; apply H4; rewrite E1; auto with datatypes.
intros (HH1, HH2).
cut (ln3 = [] /\ ln4 = [] /\ a = S n); [ intros (HH3, (HH4, HH5)) | generalize HH1; rewrite H7; case ln4; simpl in |- *; [ case ln3; try (intros; discriminate); (intros HH6; injection HH6; auto) | intros n0 l; case l; simpl in |- *; intros; discriminate ] ].
case height_pred_larger_ex with (1 := H); auto.
intros n1; rewrite <- HH5; intros (HH6, HH7).
contradict HH7; apply lt_not_le; apply H4; rewrite E1; auto with datatypes.
