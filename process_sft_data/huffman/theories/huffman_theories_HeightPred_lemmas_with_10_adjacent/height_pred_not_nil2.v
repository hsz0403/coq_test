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

Theorem height_pred_ordered_cover : forall (n : nat) (ln : list nat) (t : btree A) (l : list (btree A)), height_pred n ln l t -> ordered_cover l t.
Proof using.
Admitted.

Theorem height_pred_not_nil1 : forall (n : nat) (ln : list nat) (t : btree A) (l : list (btree A)), height_pred n ln l t -> ln <> [].
Proof using.
intros n ln t l H; elim H; simpl in |- *; auto.
intros; discriminate.
intros n0 ln1 ln2 t1 t2 l1 l2 H0; case ln1; simpl in |- *; auto.
Admitted.

Theorem height_pred_length : forall (n : nat) (ln : list nat) (t : btree A) (l : list (btree A)), height_pred n ln l t -> length ln = length l.
Proof using.
intros n ln t l H; elim H; simpl in |- *; auto.
Admitted.

Theorem height_pred_weight : forall (n : nat) (ln : list nat) (t : btree A) (l : list (btree A)), height_pred n ln l t -> n * sum_leaves f t + weight_tree f t = prod2list f ln l.
Proof using.
intros n ln t l H; elim H; simpl in |- *; auto.
intros n0 ln1 ln2 t1 t2 l1 l2 H0 H1 H2 H3.
rewrite prod2list_app; auto with arith.
rewrite <- H3; rewrite <- H1; ring.
Admitted.

Theorem ordered_cover_height_pred : forall (n : nat) (t : btree A) (l : list (btree A)), ordered_cover l t -> exists ln : list nat, height_pred n ln l t.
Proof using.
intros n t l H; generalize n; elim H; clear n t l H.
intros t l n; exists (n :: []); auto.
intros t1 t2 l1 l2 l3 H H0 H1 H2 n.
case (H0 (S n)); intros ln1 HH1.
case (H2 (S n)); intros ln2 HH2.
Admitted.

Theorem height_pred_larger : forall (n n1 : nat) (ln : list nat) (t : btree A) (l : list (btree A)), height_pred n ln l t -> In n1 ln -> n <= n1.
Proof using.
intros n n1 ln t l H; generalize n1; elim H; clear H n ln t l n1; auto with arith.
intros n t n1 [H2| H2]; [ rewrite H2 | case H2 ]; auto.
intros n ln1 ln2 t1 t2 l1 l2 H H0 H1 H2 n1 H3; apply le_trans with (S n); auto with arith.
Admitted.

Theorem height_pred_larger_strict : forall (n n1 : nat) (ln : list nat) (t : btree A) (l : list (btree A)), height_pred n ln l t -> In n1 ln -> n < n1 \/ ln = n :: [] /\ l = t :: [].
Proof using.
intros n n1 ln t l H; generalize n1; elim H; clear H n ln t l n1; auto.
intros n ln1 ln2 t1 t2 l1 l2 H H0 H1 H2 n1 H3; left; apply lt_le_trans with (S n); auto.
case in_app_or with (1 := H3).
intros H4; apply height_pred_larger with (1 := H); auto.
Admitted.

Theorem height_pred_larger_ex : forall (n : nat) (ln : list nat) (t : btree A) (l : list (btree A)), height_pred n ln l t -> exists n1, In n1 ln /\ n <= n1.
Proof using.
intros n ln t l H; elim H; clear H n ln t l.
intros n t; exists n; auto with datatypes.
intros n ln1 ln2 t1 t2 l1 l2 H (n1, (HH1, HH2)) H1 H2.
Admitted.

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
Admitted.

Theorem height_pred_disj_larger : forall (n a : nat) (ln1 ln2 : list nat) (t : btree A) (l : list (btree A)), height_pred n (ln1 ++ a :: ln2) l t -> (forall n1 : nat, In n1 ln1 -> n1 < a) -> (forall n1 : nat, In n1 ln2 -> n1 <= a) -> (exists ln3, ln2 = a :: ln3) \/ (ln1 = [] /\ a = n /\ ln2 = []) /\ l = t :: [].
Proof using.
Admitted.

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
Admitted.

Theorem height_pred_disj_larger2 : forall (n a : nat) (ln1 ln2 : list nat) (t : btree A) (l : list (btree A)), height_pred n (ln1 ++ a :: ln2) l t -> (exists n1, In n1 ln1 /\ a <= n1) \/ (exists n1, In n1 ln2 /\ a <= n1) \/ (ln1 = [] /\ a = n /\ ln2 = []) /\ l = t :: [].
Proof using.
intros n a ln1 ln2 t l H; case height_pred_disj_larger2_aux with (a := a) (ln1 := ln1) (ln2 := ln2) (1 := H); auto.
intros [H1| (H1, H2)]; auto.
generalize H1 H2; case ln1; simpl in |- *; [ intros H3; injection H3; auto with datatypes | idtac ].
intros H0 H4 H5; repeat right; auto.
Admitted.

Theorem height_pred_not_nil2 : forall (n : nat) (ln : list nat) (t : btree A) (l : list (btree A)), height_pred n ln l t -> l <> [].
Proof using.
intros n ln t l H; elim H; simpl in |- *; auto.
intros; discriminate.
intros n0 ln1 ln2 t1 t2 l1 l2 H0; case l1; simpl in |- *; auto.
intros; discriminate.
