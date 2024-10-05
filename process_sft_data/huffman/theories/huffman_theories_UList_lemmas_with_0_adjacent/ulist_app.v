Require Import List.
Require Import Arith.
From Huffman Require Import Permutation.
Section UniqueList.
Variable A : Type.
Variable eqA_dec : forall a b : A, {a = b} + {a <> b}.
Inductive ulist : list A -> Prop := | ulist_nil : ulist [] | ulist_cons : forall a l, ~ In a l -> ulist l -> ulist (a :: l).
Hint Constructors ulist : core.
Definition ulist_dec : forall l, {ulist l} + {~ ulist l}.
Proof.
intros l; elim l; auto.
intros a l1 [H| H]; auto.
case (In_dec eqA_dec a l1); intros H2; auto.
right; red in |- *; intros H1; inversion H1; auto.
right; contradict H; apply ulist_inv with (1 := H).
Defined.
End UniqueList.
Arguments ulist [A].
Hint Constructors ulist : core.

Theorem ulist_app : forall l1 l2, ulist l1 -> ulist l2 -> (forall a : A, In a l1 -> In a l2 -> False) -> ulist (l1 ++ l2).
Proof using.
intros L1; elim L1; simpl in |- *; auto.
intros a l H l2 H0 H1 H2; apply ulist_cons; simpl in |- *; auto.
red in |- *; intros H3; case in_app_or with (1 := H3); auto; intros H4.
inversion H0; auto.
apply H2 with a; auto.
apply H; auto.
apply ulist_inv with (1 := H0); auto.
intros a0 H3 H4; apply (H2 a0); auto.
