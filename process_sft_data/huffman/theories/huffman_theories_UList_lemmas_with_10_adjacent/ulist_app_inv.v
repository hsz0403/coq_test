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

Theorem ulist_inv : forall a l, ulist (a :: l) -> ulist l.
Proof using.
Admitted.

Theorem ulist_app : forall l1 l2, ulist l1 -> ulist l2 -> (forall a : A, In a l1 -> In a l2 -> False) -> ulist (l1 ++ l2).
Proof using.
intros L1; elim L1; simpl in |- *; auto.
intros a l H l2 H0 H1 H2; apply ulist_cons; simpl in |- *; auto.
red in |- *; intros H3; case in_app_or with (1 := H3); auto; intros H4.
inversion H0; auto.
apply H2 with a; auto.
apply H; auto.
apply ulist_inv with (1 := H0); auto.
Admitted.

Theorem ulist_app_inv_l : forall l1 l2 : list A, ulist (l1 ++ l2) -> ulist l1.
Proof using.
intros l1; elim l1; simpl in |- *; auto.
intros a l H l2 H0; inversion H0; apply ulist_cons; auto.
contradict H3; auto with datatypes.
Admitted.

Theorem ulist_app_inv_r : forall l1 l2 : list A, ulist (l1 ++ l2) -> ulist l2.
Proof using.
intros l1; elim l1; simpl in |- *; auto.
Admitted.

Definition ulist_dec : forall l, {ulist l} + {~ ulist l}.
Proof.
intros l; elim l; auto.
intros a l1 [H| H]; auto.
case (In_dec eqA_dec a l1); intros H2; auto.
right; red in |- *; intros H1; inversion H1; auto.
Admitted.

Theorem ulist_perm : forall l1 l2 : list A, permutation l1 l2 -> ulist l1 -> ulist l2.
Proof using.
intros l1 l2 H; elim H; clear H l1 l2; simpl in |- *; auto.
intros a l1 l2 H0 H1 H2; apply ulist_cons; auto.
inversion H2; auto.
contradict H4; apply permutation_in with (1 := permutation_sym _ _ _ H0); auto.
inversion H2; auto.
intros a b L H0; apply ulist_cons; auto.
inversion H0; auto.
inversion H3; auto.
simpl in |- *; contradict H7; case H7; auto.
intros H8; case H2; rewrite H8; simpl in |- *; auto.
apply ulist_cons; auto.
inversion H0; auto.
contradict H2; simpl in |- *; auto.
inversion H0; auto.
Admitted.

Theorem ulist_app_inv : forall l1 l2 (a : A), ulist (l1 ++ l2) -> In a l1 -> In a l2 -> False.
Proof using.
intros l1; elim l1; simpl in |- *; auto.
intros a l H l2 a0 H0 [H1| H1] H2.
inversion H0; auto.
case H5; rewrite H1; auto with datatypes.
apply (H l2 a0); auto.
apply ulist_inv with (1 := H0); auto.
