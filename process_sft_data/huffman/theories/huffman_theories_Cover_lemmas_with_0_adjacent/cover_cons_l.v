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

Theorem cover_cons_l : forall t1 t2 l1, cover l1 t1 -> cover (t2 :: l1) (node t2 t1).
Proof using.
intros t1 t2 l1 H; elim H; clear t1 l1 H; simpl in |- *; auto.
intros t; apply cover_node with (l2 := []) (t1 := t2) (t2 := t); auto.
intros l1 l2 t1 t0 t3 H H0 H1.
apply cover_node with (l2 := t2 :: l2) (t1 := t1) (t2 := t0); auto.
apply permutation_trans with (t2 :: t1 :: t0 :: l2); auto.
apply permutation_trans with (t1 :: t2 :: t0 :: l2); auto.
apply cover_permutation with (1 := H1); auto.
