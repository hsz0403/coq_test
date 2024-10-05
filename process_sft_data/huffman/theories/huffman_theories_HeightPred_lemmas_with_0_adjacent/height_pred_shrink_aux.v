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

Theorem height_pred_shrink_aux : forall (n : nat) (ln : list nat) (t : btree A) (l : list (btree A)), height_pred n ln l t -> forall l1 l2 ln1 ln2 a b t1 t2, ln = ln1 ++ a :: b :: ln2 -> (forall n1 : nat, In n1 ln1 -> n1 < a) -> (forall n1 : nat, In n1 (b :: ln2) -> n1 <= a) -> length ln1 = length l1 -> l = l1 ++ t1 :: t2 :: l2 -> height_pred n (ln1 ++ pred a :: ln2) (l1 ++ node t1 t2 :: l2) t.
Proof using.
intros n ln t l H; elim H; clear n ln t l H; auto.
intros n t l1 l2 ln1 ln2 a b t1 t2; case ln1; try (simpl in |- *; intros; discriminate).
intros n0 l0; case l0; try (simpl in |- *; intros; discriminate).
intros n ln1 ln2 t1 t2 l1 l2 H H0 H1 H2 l0 l3 ln0 ln3 a b t0 t3 H3 H4 H5 H6 H7.
cut (length ln1 = length l1); [ intros Eq2 | apply height_pred_length with (1 := H) ].
cut (length ln2 = length l2); [ intros Eq3 | apply height_pred_length with (1 := H1) ].
cut (length ln3 = length l3); [ intros Eq4 | apply plus_reg_l with (length (ln0 ++ a :: b :: [])); rewrite <- app_length; rewrite app_ass; simpl in |- *; rewrite <- H3; repeat rewrite app_length; simpl in |- *; rewrite Eq2; rewrite Eq3; rewrite <- app_length; rewrite H7; repeat rewrite app_length; simpl in |- *; repeat rewrite (fun x y => plus_comm x (S y)); simpl in |- *; rewrite plus_comm; auto ].
case app_inv_app2 with (1 := H3); auto.
intros (ln4, Hp1).
cut (ln3 = ln4 ++ ln2); [ intros E1 | apply app_inv_head with (l := ln0 ++ a :: b :: []); repeat rewrite app_ass; simpl in |- *; rewrite <- H3; rewrite Hp1; repeat rewrite app_ass; auto ].
replace (ln0 ++ pred a :: ln3) with ((ln0 ++ pred a :: ln4) ++ ln2); [ idtac | rewrite app_ass; rewrite E1; auto ].
cut (l3 = firstn (length ln4) l3 ++ l2).
intros HH; replace (l0 ++ node t0 t3 :: l3) with ((l0 ++ node t0 t3 :: firstn (length ln4) l3) ++ l2); [ idtac | pattern l3 at 2 in |- *; rewrite HH; rewrite app_ass; auto ].
apply height_pred_node; auto.
apply H0 with (1 := Hp1); auto.
intros n1 HH1; (apply H5; auto).
simpl in HH1; case HH1; intros H9; try rewrite H9; auto with datatypes.
rewrite E1; auto with datatypes.
apply app_inv_tail with (l := l2).
repeat rewrite app_ass; apply trans_equal with (1 := H7); auto.
pattern l3 at 1 in |- *; rewrite HH; auto.
apply sym_equal; apply trans_equal with (2 := firstn_skipn (length ln4) l3).
apply f_equal2 with (f := app (A:=btree A)); auto.
apply trans_equal with (skipn (length l1 - length l1) l2).
rewrite <- minus_n_n; simpl in |- *; auto.
rewrite <- skipn_le_app1; auto.
rewrite H7.
rewrite <- Eq2; rewrite Hp1.
rewrite skipn_le_app1.
rewrite app_length.
rewrite H6; rewrite minus_plus; simpl in |- *; auto.
rewrite <- H6; rewrite app_length; simpl in |- *; auto with arith.
intros [(ln4, HH)| (HH1, HH2)].
cut (ln0 = ln1 ++ ln4); [ intros E1 | apply app_inv_tail with (l := a :: b :: ln3); rewrite <- H3; rewrite HH; rewrite app_ass; auto ].
cut (l0 = l1 ++ skipn (length l1) l0).
intros Eq1; rewrite Eq1; rewrite E1; repeat rewrite app_ass.
apply height_pred_node; auto.
apply H2 with (b := b); auto.
intros n1 H8; apply H4; (rewrite E1; auto with datatypes).
rewrite length_skipn; rewrite <- Eq2; rewrite <- H6; rewrite <- length_skipn; rewrite E1; rewrite skipn_le_app2; auto; rewrite skipn_length_all; simpl in |- *; auto.
apply app_inv_head with (l := l1).
rewrite <- app_ass; rewrite <- Eq1; auto.
apply sym_equal; apply trans_equal with (2 := firstn_skipn (length l1) l0).
apply f_equal2 with (f := app (A:=btree A)); auto.
apply trans_equal with (firstn (length l1) (l1 ++ l2)).
rewrite firstn_le_app1; auto; rewrite <- minus_n_n; simpl in |- *; auto with datatypes.
rewrite H7; rewrite firstn_le_app2; auto.
rewrite <- H6; rewrite <- Eq2; rewrite E1; rewrite app_length; auto with arith.
rewrite HH1 in H; case height_pred_disj_larger2 with (1 := H); simpl in |- *; auto.
intros (n1, (HH3, HH4)); contradict HH4; auto with arith.
intros [(n1, (HH3, HH4))| ((HH3, (HH4, HH5)), HH6)]; [ case HH3 | idtac ].
case height_pred_larger_strict with (1 := H1) (n1 := b); auto.
rewrite HH2; auto with datatypes.
rewrite <- HH4; intros HH7; contradict HH7; apply le_not_lt; auto with arith datatypes.
intros (H8, H9); rewrite HH4; rewrite HH3; simpl in |- *.
cut (l0 = []); [ intros HM1; rewrite HM1 | idtac ].
cut (ln3 = []); [ intros HM2; rewrite HM2 | idtac ].
replace l3 with (nil (A:=btree A)); simpl in |- *; auto.
rewrite HH6 in H7; rewrite H9 in H7; rewrite HM1 in H7; simpl in H7; injection H7.
intros Ht1 Ht2 Ht3; rewrite Ht2; rewrite Ht3; auto.
generalize Eq4; rewrite HM2; case l3; simpl in |- *; auto; intros; discriminate.
rewrite HH2 in H8; injection H8; auto.
generalize H6; rewrite HH3; case l0; simpl in |- *; auto; intros; discriminate.
