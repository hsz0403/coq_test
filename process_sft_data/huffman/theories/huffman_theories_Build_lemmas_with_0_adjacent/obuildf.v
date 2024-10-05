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
