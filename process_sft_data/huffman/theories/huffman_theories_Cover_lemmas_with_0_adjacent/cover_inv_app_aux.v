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

Lemma cover_inv_app_aux : forall t t1 t2 l, cover l t -> t = node t1 t2 -> l = node t1 t2 :: [] \/ (exists l1, (exists l2, (cover l1 t1 /\ cover l2 t2) /\ permutation l (l1 ++ l2))).
Proof using.
intros t t1 t2 l H; elim H.
intros t0 Ht0; rewrite Ht0; auto with datatypes.
intros l1 l2 t0 t3 t4 H0 H1 H2 H3; right.
case H2; auto.
intros H4.
exists (t1 :: []); exists (t2 :: []); simpl in |- *; repeat (split; auto).
injection H4; intros H5 H6 H7; rewrite <- H5; rewrite <- H6; rewrite <- H7; auto.
clear H2 H3; intros (l3, (l4, ((Hl1, Hl2), Hl3))).
case (in_app_or l3 l4 (node t0 t3)).
apply permutation_in with (1 := Hl3); auto with datatypes.
intros H2; case in_ex_app with (1 := H2).
intros l5 (l6, Hl5).
exists (t0 :: t3 :: l5 ++ l6); exists l4; repeat (split; auto).
apply cover_node with (l2 := l5 ++ l6) (t1 := t0) (t2 := t3); auto.
apply cover_permutation with (1 := Hl1).
rewrite Hl5.
apply permutation_trans with (node t0 t3 :: l6 ++ l5); auto.
apply (permutation_app_swap _ l5 (node t0 t3 :: l6)).
apply permutation_trans with (1 := H0).
simpl in |- *; repeat apply permutation_skip.
apply permutation_inv with (a := node t0 t3).
apply permutation_trans with (1 := Hl3).
rewrite Hl5; auto.
change (permutation ((l5 ++ node t0 t3 :: l6) ++ l4) ((node t0 t3 :: l5 ++ l6) ++ l4)) in |- *.
apply permutation_app_comp; auto.
apply permutation_trans with ((node t0 t3 :: l6) ++ l5); auto.
simpl in |- *; auto.
intros H2; case in_ex_app with (1 := H2).
intros l5 (l6, Hl5).
exists l3; exists (t0 :: t3 :: l5 ++ l6); repeat (split; auto).
apply cover_node with (l2 := l5 ++ l6) (t1 := t0) (t2 := t3); auto.
apply cover_permutation with (1 := Hl2).
rewrite Hl5.
apply permutation_trans with (node t0 t3 :: l6 ++ l5); auto.
apply (permutation_app_swap _ l5 (node t0 t3 :: l6)).
apply permutation_trans with (1 := H0).
apply permutation_trans with ((t0 :: t3 :: l5 ++ l6) ++ l3); auto.
simpl in |- *; repeat apply permutation_skip.
apply permutation_inv with (a := node t0 t3).
apply permutation_trans with (1 := Hl3).
rewrite Hl5.
apply permutation_trans with ((l5 ++ node t0 t3 :: l6) ++ l3); auto.
change (permutation ((l5 ++ node t0 t3 :: l6) ++ l3) ((node t0 t3 :: l5 ++ l6) ++ l3)) in |- *; auto.
apply permutation_app_comp; auto.
apply permutation_trans with ((node t0 t3 :: l6) ++ l5); auto.
simpl in |- *; auto.
