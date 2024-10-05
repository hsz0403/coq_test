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

Theorem unique_key_map : forall (A B C D : Type) l (f : A * B -> C * D), unique_key l -> (forall a b, fst (f a) = fst (f b) -> fst a = fst b) -> unique_key (map f l).
Proof using.
intros A B C D l f H; elim H; simpl in |- *; auto.
intros a b l0 H0 H1 H2 H3.
case_eq (f (a, b)); intros fa fb Hf; auto.
apply unique_key_cons; auto.
generalize H0; elim l0; simpl in |- *; auto.
intros (a0, b0) l1 H4 H5 b1; red in |- *; intros [H6| H6].
case (H5 b0); left; apply f_equal2 with (f := pair (A:=A) (B:=B)); auto.
change (fst (a0, b0) = fst (a, b)) in |- *.
apply H3; auto.
rewrite H6; rewrite Hf; simpl in |- *; auto.
generalize H6; change (~ In (fa, b1) (map f l1)) in |- *.
apply H4.
intros b2; red in |- *; intros H7.
case (H5 b2); auto.
