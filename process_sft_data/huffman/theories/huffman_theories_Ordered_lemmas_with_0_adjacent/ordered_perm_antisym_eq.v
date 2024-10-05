From Huffman Require Export Permutation.
From Huffman Require Export AuxLib.
Section ordered.
Variable A : Type.
Variable order : A -> A -> Prop.
Hypothesis order_trans : forall a b c : A, order a b -> order b c -> order a c.
Inductive ordered : list A -> Prop := | ordered_nil : ordered [] | ordered_one : forall a : A, ordered (a :: []) | ordered_cons : forall (a b : A) (l : list A), order a b -> ordered (b :: l) -> ordered (a :: b :: l).
Hint Constructors ordered : core.
End ordered.
Hint Constructors ordered : core.
Arguments ordered [A].

Theorem ordered_perm_antisym_eq : (forall a b : A, order a b -> order b a -> a = b) -> forall l1 l2 : list A, permutation l1 l2 -> ordered l1 -> ordered l2 -> l1 = l2.
Proof using A order order_trans.
intros antisym l1; elim l1; clear l1; simpl in |- *; auto.
intros l2 H1 H2 H3; apply sym_equal; apply permutation_nil_inv.
apply permutation_sym; auto.
intros a l1 Rec l2; case l2; simpl in |- *.
intros H; absurd (length (a :: l1) = length (A:=A) []).
simpl in |- *; red in |- *; intros; discriminate.
apply permutation_length; auto.
intros a0 l H H0 H1.
cut (a = a0).
intros H3; apply f_equal2 with (f := cons (A:=A)); auto.
apply Rec; auto.
apply permutation_inv with (a := a); auto.
pattern a at 2 in |- *; rewrite H3; auto.
apply ordered_inv with (1 := H0); auto.
apply ordered_inv with (1 := H1); auto.
generalize (permutation_in _ a _ _ H); simpl in |- *; (intros H2; case H2; auto; clear H2; intros H2).
generalize (permutation_in _ a0 _ _ (permutation_sym _ _ _ H)); simpl in |- *; (intros H3; case H3; auto; clear H3; intros H3).
apply antisym.
apply ordered_trans with (1 := H0); auto.
apply ordered_trans with (1 := H1); auto.
