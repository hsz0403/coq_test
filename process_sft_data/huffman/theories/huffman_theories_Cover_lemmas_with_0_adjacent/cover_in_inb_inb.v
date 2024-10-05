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

Theorem cover_in_inb_inb : forall l t1 t2 t3, cover l t1 -> In t2 l -> inb t3 t2 -> inb t3 t1.
Proof using.
intros l t1 t2 t3 H; generalize t2 t3; elim H; clear H l t1 t2 t3; auto with datatypes.
simpl in |- *; intros t t2 t3 [H1| H1]; auto.
rewrite H1; auto.
case H1.
intros l1 l2 t1 t2 t3 H H0 H1 t0 t4 H2 H3.
cut (In t0 (t1 :: t2 :: l2)); auto.
simpl in |- *; intros [H4| [H4| H4]]; auto with datatypes.
apply (H1 (node t1 t2)); simpl in |- *; auto.
rewrite H4; auto.
apply (H1 (node t1 t2)); simpl in |- *; auto.
rewrite H4; auto.
apply (H1 t0); simpl in |- *; auto.
apply permutation_in with (1 := H); simpl in |- *; auto.
