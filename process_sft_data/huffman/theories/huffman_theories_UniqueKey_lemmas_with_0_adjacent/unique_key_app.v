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

Theorem unique_key_app : forall l1 l2, unique_key l1 -> unique_key l2 -> (forall a b c, In (a, b) l1 -> In (a, c) l2 -> False) -> unique_key (l1 ++ l2).
Proof using.
intros l1; elim l1; simpl in |- *; auto.
intros (a1, ll1) l H l2 H0 H1 H2; apply unique_key_cons; auto.
intros b; red in |- *; intros H3.
case in_app_or with (1 := H3).
change (~ In (a1, b) l) in |- *; apply unique_key_in with (1 := H0).
intros H4; apply (H2 a1 ll1 b); auto.
apply H; auto.
apply unique_key_inv with (1 := H0); auto.
intros a b c H3 H4; apply (H2 a b c); auto.
