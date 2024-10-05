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

Theorem ulist_app_inv_l : forall l1 l2 : list A, ulist (l1 ++ l2) -> ulist l1.
Proof using.
intros l1; elim l1; simpl in |- *; auto.
intros a l H l2 H0; inversion H0; apply ulist_cons; auto.
contradict H3; auto with datatypes.
apply H with l2; auto.
