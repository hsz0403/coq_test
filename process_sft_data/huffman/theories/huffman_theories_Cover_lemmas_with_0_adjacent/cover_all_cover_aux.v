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

Theorem cover_all_cover_aux : forall (n : nat) l t, n = length l -> cover l t -> In t (all_cover_aux l n).
Proof using.
intros n; elim n; simpl in |- *; auto.
intros l; case l; simpl in |- *; auto.
intros t H H0; inversion H0.
generalize (permutation_nil_inv _ _ (permutation_sym _ _ _ H1)); intros; discriminate.
intros; discriminate.
intros n0 H l t H0 H1; inversion H1.
simpl in |- *; auto.
apply in_flat_map_in with (t1 :: t2 :: l2); auto.
apply H; auto.
apply eq_add_S; apply trans_equal with (1 := H0).
apply trans_equal with (length (t1 :: t2 :: l2)); auto.
apply permutation_length; auto.
apply permutation_all_permutations; auto.
apply permutation_sym; auto.
