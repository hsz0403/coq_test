From Huffman Require Export Cover.
Section OrderedCover.
Variable A : Type.
Inductive ordered_cover : list (btree A) -> btree A -> Prop := | ordered_cover_one : forall (t : btree A) (l : list (btree A)), ordered_cover (t :: []) t | ordered_cover_node : forall (t1 t2 : btree A) (l1 l2 l3 : list (btree A)), ordered_cover l1 t1 -> ordered_cover l2 t2 -> ordered_cover (l1 ++ l2) (node t1 t2).
Hint Resolve ordered_cover_one ordered_cover_node : core.
End OrderedCover.
Arguments ordered_cover [A].
Hint Resolve ordered_cover_one ordered_cover_node : core.

Theorem ulist_ordered_cover : forall l1 l2 t, ordered_cover l1 t -> ulist l2 -> l1 = map (fun x : A => leaf x) l2 -> all_leaves t = l2.
Proof using.
intros l1 l2 t H; generalize l2; elim H; clear H l1 l2 t; simpl in |- *; auto.
intros t l l2; case l2; simpl in |- *; auto.
intros; discriminate.
intros a0 l0 H H0; injection H0; intros H1 H2; rewrite H2; auto.
generalize H1; case l0; simpl in |- *; auto.
intros; discriminate.
intros t1 t2 l1 l2 l3 H H0 H1 H2 l0 H3 H4.
cut ((exists l3 : list A, l1 = map (fun x : A => leaf x) l3) /\ (exists l4 : list A, l2 = map (fun x : A => leaf x) l4)).
intros ((l4, HH1), (l5, HH2)).
cut (l0 = l4 ++ l5); [ intros HH3 | idtac ].
rewrite HH3.
apply f_equal2 with (f := app (A:=A)).
apply H0; auto.
apply ulist_app_inv_l with (l2 := l5); rewrite <- HH3; auto.
apply H2; auto.
apply ulist_app_inv_r with (l1 := l4); rewrite <- HH3; auto.
rewrite HH2 in H4; rewrite HH1 in H4.
rewrite <- map_app in H4.
generalize H4; generalize (l4 ++ l5); elim l0; simpl in |- *; auto.
intros l; case l; simpl in |- *; auto.
intros; discriminate.
intros a0 l H5 l6; case l6; simpl in |- *; auto.
intros; discriminate.
intros a1 l7 H6; apply f_equal2 with (f := cons (A:=A)); auto.
injection H6; auto.
injection H6; auto.
generalize H4; generalize l2 l0; elim l1; simpl in |- *; auto.
intros l4 l5 H5; split; [ exists [] | exists l5 ]; auto.
intros a0 l H5 l4 l5; case l5; simpl in |- *; auto.
intros; discriminate.
intros a1 l6 H6; case (H5 l4 l6); auto.
injection H6; auto.
intros (l7, HH5) (l8, HH6); split; [ exists (a1 :: l7) | exists l8 ]; simpl in |- *; auto.
apply f_equal2 with (f := cons (A:=btree A)); auto.
Admitted.

Theorem cover_ordered_cover : forall (l1 : list (btree A)) (t : btree A), cover l1 t -> exists l2, permutation l1 l2 /\ ordered_cover l2 t.
Proof using.
intros l1; elim l1 using list_length_ind.
intros l0 H t; case t.
intros a H1; rewrite cover_inv_leaf with (1 := H1).
exists (leaf a :: []); auto.
intros t1 t2 H1; case cover_inv_app with (1 := H1).
intros H2; exists l0; split; auto; rewrite H2; auto.
intros (l2, (l3, ((HH1, HH2), HH3))).
case H with (2 := HH1); auto.
rewrite permutation_length with (1 := HH3).
generalize HH2; rewrite app_length; case l3; simpl in |- *; auto with arith.
intros HH4; case cover_not_nil with (1 := HH4); auto.
intros; rewrite plus_comm; simpl in |- *; auto with arith.
intros l4 (HP1, HP2).
case H with (2 := HH2); auto.
rewrite permutation_length with (1 := HH3).
generalize HH1; rewrite app_length; case l2; simpl in |- *; auto with arith.
intros HH4; case cover_not_nil with (1 := HH4); auto.
intros l5 (HP3, HP4).
exists (l4 ++ l5); split; auto.
apply permutation_trans with (1 := HH3); auto.
