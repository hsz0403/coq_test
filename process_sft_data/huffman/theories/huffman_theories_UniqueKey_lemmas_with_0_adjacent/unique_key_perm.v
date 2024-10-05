From Huffman Require Export AuxLib.
From Huffman Require Export Permutation.
From Huffman Require Export UList.
Section UniqueKey.
Variables (A : Type) (B : Type).
Inductive unique_key : list (A * B) -> Prop := | unique_key_nil : unique_key [] | unique_key_cons : forall (a : A) (b : B) l, (forall b : B, ~ In (a, b) l) -> unique_key l -> unique_key ((a, b) :: l).
Hint Constructors unique_key : core.
End UniqueKey.
Hint Constructors unique_key : core.
Arguments unique_key [A B].
Hint Resolve unique_key_app unique_key_map : core.

Theorem unique_key_perm : forall l1 l2, permutation l1 l2 -> unique_key l1 -> unique_key l2.
Proof using.
intros l1 l2 H; elim H; auto.
intros (a1, b1) L1 L2 H0 H1 H2; apply unique_key_cons.
intros b; red in |- *; intros H3; case (unique_key_in _ _ b _ H2).
apply permutation_in with (2 := H3); auto.
apply permutation_sym; auto.
apply H1; apply unique_key_inv with (1 := H2); auto.
intros (a1, b1) (a2, b2) L H0; apply unique_key_cons.
intros b; red in |- *; simpl in |- *; intros [H1| H1].
case (unique_key_in _ _ b2 _ H0); auto.
injection H1; intros H2 H3; rewrite H3; simpl in |- *; auto.
case (unique_key_in _ _ b _ (unique_key_inv _ _ H0)); auto.
apply unique_key_cons.
intros b; red in |- *; simpl in |- *; intros H1; case (unique_key_in _ _ b _ H0); simpl in |- *; auto.
apply unique_key_inv with (a := (a2, b2)); apply unique_key_inv with (1 := H0).
