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

Theorem ulist_unique_key : forall l : list (A * B), ulist (map (fst (B:=_)) l) -> unique_key l.
Proof using.
intros l; elim l; simpl in |- *; auto.
intros a; case a.
intros a0 b l0 H H0; apply unique_key_cons; auto.
intros b0; red in |- *; intros H1; absurd (In a0 (map (fst (B:=_)) l0)); auto.
inversion H0; auto.
change (In (fst (a0, b0)) (map (fst (B:=_)) l0)) in |- *; auto with datatypes.
apply in_map; auto.
apply H; apply ulist_inv with (1 := H0); auto.
