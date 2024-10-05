From Huffman Require Export Code.
From Huffman Require Export ISort.
Require Export Compare_dec.
From Huffman Require Export Weight.
From Huffman Require Export UniqueKey.
Require Import ArithRing.
Section Tree.
Variable A : Type.
Variable eqA_dec : forall a b : A, {a = b} + {a <> b}.
Variable empty : A.
Inductive btree : Type := | leaf : A -> btree | node : btree -> btree -> btree.
Inductive inb : btree -> btree -> Prop := | inleaf : forall t : btree, inb t t | innodeL : forall t t1 t2 : btree, inb t t1 -> inb t (node t1 t2) | innodeR : forall t t1 t2 : btree, inb t t2 -> inb t (node t1 t2).
Hint Constructors inb : core.
Fixpoint number_of_nodes (b : btree) : nat := match b with | leaf _ => 0 | node b1 b2 => S (number_of_nodes b1 + number_of_nodes b2) end.
Definition btree_dec : forall a b : btree, {a = b} + {a <> b}.
Proof.
intros a; elim a.
intros a1 b; case b.
intros b1; case (eqA_dec a1 b1).
intros e; left; rewrite e; auto.
intros e; right; contradict e; inversion e; auto.
intros b0 b1; right; red in |- *; intros H; discriminate.
intros b H b0 H0 b1; case b1.
intros a0; right; red in |- *; intros H1; discriminate.
intros b2 b3; case (H b2); intros H1.
case (H0 b3); intros H2.
left; rewrite H1; rewrite H2; auto.
right; rewrite H1; contradict H2; inversion H2; auto.
right; contradict H1; inversion H1; auto.
Defined.
Definition inb_dec : forall a p, {inb a p} + {~ inb a p}.
Proof.
intros a; elim a; simpl in |- *; auto; clear a.
intros a p; elim p; simpl in |- *; auto; clear p.
intros a1; case (eqA_dec a a1); intros Ha.
left; rewrite Ha; simpl in |- *; auto.
right; red in |- *; contradict Ha; inversion Ha; auto.
intros b [H| H]; auto.
intros b0 [H1| H1]; auto.
right; red in |- *; intros H2; inversion H2.
case H; auto.
case H1; auto.
intros b H b0 H0 p; elim p; auto.
intros a; right; red in |- *; intros H1; inversion H1.
intros b1 H1 b2 H2.
case H1; intros H3; auto.
case H2; intros H4; auto.
case (btree_dec (node b b0) (node b1 b2)); intros H5.
left; rewrite H5; auto.
right; red in |- *; intros H6; inversion H6; auto.
case H5; rewrite H9; rewrite H10; auto.
Defined.
Fixpoint all_leaves (t : btree) : list A := match t with | leaf a => a :: [] | node t1 t2 => all_leaves t1 ++ all_leaves t2 end.
Definition distinct_leaves (t : btree) : Prop := forall t0 t1 t2 : btree, inb (node t1 t2) t -> inb t0 t1 -> inb t0 t2 -> False.
Hint Resolve distinct_leaves_leaf : core.
Definition distinct_leaves_dec : forall a, {distinct_leaves a} + {~ distinct_leaves a}.
Proof.
intros a; case (ulist_dec A eqA_dec (all_leaves a)); intros H.
left; apply all_leaves_unique; auto.
right; contradict H; apply all_leaves_ulist; auto.
Defined.
Fixpoint compute_code (a : btree) : list (A * list bool) := match a with | leaf b => (b, []) :: [] | node l1 l2 => map (fun v : A * list bool => match v with | (a1, b1) => (a1, false :: b1) end) (compute_code l1) ++ map (fun v : A * list bool => match v with | (a1, b1) => (a1, true :: b1) end) (compute_code l2) end.
Hint Resolve length_compute_lt_O : core.
End Tree.
Arguments leaf [A].
Arguments node [A].
Arguments inb [A].
Arguments all_leaves [A].
Arguments distinct_leaves [A].
Arguments compute_code [A].
Arguments number_of_nodes [A].
Hint Constructors inb : core.
Hint Resolve distinct_leaves_leaf : core.
Hint Resolve length_compute_lt_O : core.

Theorem btree_unique_prefix1 : forall (t : btree) (a1 a2 : A) (lb1 lb2 : list bool), In (a1, lb1) (compute_code t) -> In (a2, lb2) (compute_code t) -> is_prefix lb1 lb2 -> a1 = a2.
Proof using.
intros t; elim t; simpl in |- *.
intros leaf1 a1 a2 lb1 lb2 H1 H2.
case H1; intros H3; [ injection H3 | case H3 ].
case H2; intros H4; [ injection H4 | case H4 ].
intros H H0 H5 H6 H7; apply trans_equal with (2 := H0); auto.
intros t1 Rec1 t2 Rec2 a1 a2 lb1 lb2 H1 H2.
case (in_app_or _ _ _ H1); case (in_app_or _ _ _ H2); clear H1 H2; intros H2 H1 H3.
generalize H1 H2; inversion H3.
intros H4; case in_map_inv with (1 := H4).
intros x; case x; intros x1 x2 (H5, H6); discriminate.
intros H5 H6; apply Rec1 with (lb1 := l1) (lb2 := l2); auto.
case in_map_inv with (1 := H5).
intros x; case x.
intros a l (H7, H8); injection H8.
intros R1 R2 R3; rewrite R1; rewrite R3; auto.
case in_map_inv with (1 := H6).
intros x; case x.
intros a l (H7, H8); injection H8.
intros R1 R2 R3; rewrite R1; rewrite R3; auto.
generalize H3.
case in_map_inv with (1 := H1).
intros x; case x; intros aa1 ll1 (H4, H5).
case in_map_inv with (1 := H2).
intros x1; case x1; intros aa2 ll2 (H6, H7).
inversion H5; inversion H7; intros tH8; inversion tH8.
generalize H3.
case in_map_inv with (1 := H1).
intros x; case x; intros aa1 ll1 (H4, H5).
case in_map_inv with (1 := H2).
intros x1; case x1; intros aa2 ll2 (H6, H7).
inversion H5; inversion H7; intros tH8; inversion tH8.
generalize H1 H2; inversion H3.
intros H4; case in_map_inv with (1 := H4).
intros x; case x; intros x1 x2 (H5, H6); discriminate.
intros H5 H6; apply Rec2 with (lb1 := l1) (lb2 := l2); auto.
case in_map_inv with (1 := H5).
intros x; case x.
intros a l (H7, H8); injection H8.
intros R1 R2 R3; rewrite R1; rewrite R3; auto.
case in_map_inv with (1 := H6).
intros x; case x.
intros a l (H7, H8); injection H8.
intros R1 R2 R3; rewrite R1; rewrite R3; auto.
