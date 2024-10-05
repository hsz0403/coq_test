From Huffman Require Export BTree.
From Huffman Require Export Permutation.
Require Import ArithRing.
Section Cover.
Variable A : Type.
Variable empty : A.
Inductive cover : list (btree A) -> btree A -> Prop := | cover_one : forall t, cover (t :: []) t | cover_node : forall l1 l2 t1 t2 t3, permutation l1 (t1 :: t2 :: l2) -> cover (node t1 t2 :: l2) t3 -> cover l1 t3.
Hint Constructors cover : core.
Fixpoint all_cover_aux (l : list (btree A)) (n : nat) {struct n} : list (btree A) := match n with | O => [] | S n1 => flat_map (fun l1 => match l1 with | [] => [] | a :: [] => a :: [] | a :: b :: l2 => all_cover_aux (node a b :: l2) n1 end) (all_permutations l) end.
Definition all_cover l := all_cover_aux l (length l).
Definition cover_dec : (forall a b : A, {a = b} + {a <> b}) -> forall l t, {cover l t} + {~ cover l t}.
Proof.
intros H l t; case (In_dec (btree_dec _ H) t (all_cover l)).
intros H1; left; apply all_cover_cover; auto.
intros H1; right; contradict H1; apply cover_all_cover; auto.
Defined.
End Cover.
Arguments cover [A].
Hint Constructors cover : core.

Theorem all_cover_aux_cover : forall (n : nat) l t, n = length l -> In t (all_cover_aux l n) -> cover l t.
Proof using.
intros n; elim n; simpl in |- *; auto.
intros l t H H0; elim H0.
intros n0 H l t H0 H1.
case in_flat_map_ex with (1 := H1); clear H1.
intros x; case x; clear x.
simpl in |- *; intros (H1, H2); case H2.
intros b x; case x; clear x.
simpl in |- *; intros (H1, [H2| H2]).
rewrite <- H2.
rewrite permutation_one_inv with (a := b) (l := l); auto.
apply all_permutations_permutation; auto.
case H2.
intros b1 l1 (H1, H2).
apply cover_node with (l2 := l1) (t1 := b) (t2 := b1); auto.
apply permutation_sym; apply all_permutations_permutation; auto.
apply H; auto.
apply eq_add_S; apply trans_equal with (1 := H0).
apply trans_equal with (length (b :: b1 :: l1)); auto.
apply permutation_length.
apply permutation_sym; apply all_permutations_permutation; auto.
