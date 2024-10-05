From Huffman Require Export OneStep.
From Huffman Require Export HeightPred.
From Huffman Require Export CoverMin.
From Huffman Require Export OrderedCover.
From Huffman Require Export SubstPred.
Require Import ArithRing.
Section Build.
Variable A : Type.
Variable f : A -> nat.
Inductive build : list (btree A) -> btree A -> Prop := | build_one : forall t : btree A, build (t :: []) t | build_step : forall (t : btree A) (l1 l2 : list (btree A)), one_step f l1 l2 -> build l2 t -> build l1 t.
Definition obuildf : forall l : list (btree A), l <> [] -> ordered (sum_order f) l -> {t : btree A | build l t}.
Proof.
intros l; elim l using list_length_induction.
intros l1; case l1; clear l1.
intros H H0; case H0; auto.
intros b l0; case l0.
intros H H0 H1; exists b; auto.
apply build_one.
intros b0 l1 H H0 H1.
case (H (insert (le_sum f) (node b b0) l1)); auto.
rewrite <- permutation_length with (1 := insert_permutation _ (le_sum f) l1 (node b b0)); simpl in |- *; auto.
red in |- *; intros H2; absurd (length (node b b0 :: l1) = length (insert (le_sum f) (node b b0) l1)).
rewrite H2; simpl in |- *; intros; discriminate.
apply permutation_length with (1 := insert_permutation _ (le_sum f) l1 (node b b0)); simpl in |- *; auto.
apply insert_ordered; auto.
intros; apply le_sum_correct1; auto.
intros; apply le_sum_correct2; auto.
apply ordered_inv with (a := b0); auto.
apply ordered_inv with (a := b); auto.
intros t Ht; exists t.
apply build_step with (2 := Ht).
red in |- *; auto.
exists l1; exists b; exists b0; (repeat split; auto).
apply permutation_sym; apply insert_permutation.
Defined.
Definition buildf : forall l : list (btree A), l <> [] -> {t : btree A | build l t}.
Proof.
intros l Hl; cut (isort (le_sum f) l <> []).
intros H1; cut (ordered (sum_order f) (isort (le_sum f) l)).
intros H2; case (obuildf (isort (le_sum f) l) H1 H2).
intros t H3; exists t; auto.
apply build_permutation with (1 := H3); auto.
apply permutation_sym; apply isort_permutation; auto.
apply isort_ordered; auto.
intros; apply le_sum_correct1; auto.
intros; apply le_sum_correct2; auto.
contradict Hl; apply permutation_nil_inv; auto.
rewrite <- Hl; auto.
apply isort_permutation; auto.
Defined.
Definition build_fun : forall l : list (btree A), l <> [] -> {t : btree A | cover_min _ f l t}.
Proof.
intros l Hl; case (buildf l Hl).
intros x b; exists x.
apply build_correct; auto.
Defined.
End Build.
Arguments build [A].

Theorem build_comp : forall (l1 l2 : list (btree A)) (t1 t2 : btree A), build l1 t1 -> build l2 t2 -> weight_tree_list f l1 = weight_tree_list f l2 -> same_sum_leaves f l1 l2 -> weight_tree f t1 = weight_tree f t2.
Proof using.
intros l1 l2 t1 t2 H; generalize l2 t2; elim H; clear H l1 t1 l2 t2.
intros t l2 t2 H H0 (l3, (l4, (H1, (H2, H3)))).
generalize H0; inversion H; clear H0.
simpl in |- *; repeat rewrite <- plus_n_O; auto.
case H4.
intros l5 (t3, (t4, (H8, (H9, H10)))).
absurd (length l2 = length (t3 :: t4 :: l5)).
rewrite permutation_length with (1 := H2).
rewrite <- map_length with (f := sum_leaves f) (l := l4).
rewrite <- H3.
rewrite map_length with (f := sum_leaves f).
rewrite permutation_length with (1 := permutation_sym _ _ _ H1).
simpl in |- *; red in |- *; intros; discriminate.
apply permutation_length with (1 := H9).
intros t l1 l2 H H0 H1 l0 t2 H2 H3 H4.
inversion H2.
case H.
intros l5 (t3, (t4, (H8, (H9, H10)))).
case H4.
intros l6 (l7, (H11, (H12, H13))).
absurd (length l1 = length (t3 :: t4 :: l5)).
rewrite permutation_length with (1 := H11).
rewrite <- map_length with (f := sum_leaves f) (l := l6).
rewrite H13.
rewrite map_length with (f := sum_leaves f).
rewrite permutation_length with (1 := permutation_sym _ _ _ H12).
rewrite <- H5; simpl in |- *; red in |- *; intros; discriminate.
apply permutation_length with (1 := H9).
apply H1 with (1 := H6).
case one_step_comp with (3 := H) (4 := H5); auto.
case one_step_comp with (3 := H) (4 := H5); auto.
