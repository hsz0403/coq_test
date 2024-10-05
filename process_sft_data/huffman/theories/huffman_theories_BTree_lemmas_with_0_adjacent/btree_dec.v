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
