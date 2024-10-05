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

Theorem unique_key_in_inv : forall a l1 l2 l, unique_key l -> In (a, l1) l -> In (a, l2) l -> l1 = l2.
Proof using.
intros a l1 l2 l H; generalize a l1 l2; elim H; simpl in |- *; auto; clear H a l1 l2 l.
intros a l1 l2 H; case H.
intros a b l H H0 H1 a0 l1 l2 [H2| H2] [H3| H3].
injection H2; injection H3; intros; apply trans_equal with b; auto.
case (H l2); injection H2; intros H4 H5; rewrite H5; auto.
case (H l1); injection H3; intros H4 H5; rewrite H5; auto.
apply H1 with (1 := H2) (2 := H3); auto.
