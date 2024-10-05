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

Theorem unique_key_ulist : forall l : list (A * B), unique_key l -> ulist (map (fst (B:=_)) l).
Proof using.
intros l; elim l; simpl in |- *; auto.
intros a l0 H H0; apply ulist_cons.
inversion H0.
red in |- *; intros H5; case in_map_inv with (1 := H5).
intros (b2, l2); simpl in |- *; intros (Hb1, Hb2); case (H3 l2); auto.
rewrite Hb2; auto.
apply H; apply unique_key_inv with (1 := H0); auto.
