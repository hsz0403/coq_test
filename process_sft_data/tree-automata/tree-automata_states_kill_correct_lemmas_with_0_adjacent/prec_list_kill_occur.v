Require Import Bool.
Require Import ZArith.
From IntMap Require Import Allmaps.
Require Import bases.
Require Import defs.
Require Import semantics.
Require Import signature.
Require Import pl_path.
Require Import refcorrect.
Require Import states_kill_empty.
Require Import lattice_fixpoint.
Require Import empty_test.

Lemma prec_list_kill_occur : forall (p p' : prec_list) (b : ad) (m : Map bool), prec_list_kill m p = Some p' -> prec_occur p' b -> MapGet bool m b = Some true.
Proof.
simple induction p.
intros.
simpl in H1.
elim (pl_sum p1); intros.
rewrite H3 in H1.
elim (option_sum bool (MapGet bool m a)); intros y.
elim y.
intros x y0.
rewrite y0 in H1.
elim (bool_is_true_or_false x); intros; rewrite H4 in H1.
elim (option_sum prec_list (prec_list_kill m p0)); intros y1.
elim y1.
intros x0 y2.
rewrite y2 in H1.
inversion H1.
rewrite <- H6 in H2.
inversion H2.
rewrite <- H5.
rewrite H4 in y0.
exact y0.
exact (H _ _ _ y2 H10).
inversion H10.
rewrite y1 in H1.
inversion H1.
inversion H1.
rewrite y in H1.
inversion H1.
elim H3.
intros.
elim H4.
intros.
elim H5.
intros.
rewrite H6 in H1.
elim (option_sum bool (MapGet bool m a)); intros y.
elim y.
intros x2 y0.
rewrite y0 in H1.
elim (bool_is_true_or_false x2); intros; rewrite H7 in H1.
elim (option_sum prec_list (prec_list_kill m p0)); intros y1.
elim y1.
intros x3 y2.
rewrite y2 in H1.
elim (option_sum prec_list (prec_list_kill m (prec_cons x x0 x1))); intros y3.
elim y3.
intros x4 y4.
rewrite y4 in H1.
inversion H1.
rewrite <- H9 in H2.
inversion H2.
rewrite <- H8.
rewrite H7 in y0.
exact y0.
exact (H _ _ _ y2 H13).
rewrite <- H6 in y4.
exact (H0 _ _ _ y4 H13).
rewrite y3 in H1.
inversion H1.
rewrite <- H9 in H2.
inversion H2.
rewrite <- H8.
rewrite H7 in y0.
exact y0.
exact (H _ _ _ y2 H13).
inversion H13.
rewrite y1 in H1.
elim (option_sum prec_list (prec_list_kill m (prec_cons x x0 x1))); intros y2.
elim y2.
intros x3 y3.
rewrite y3 in H1.
inversion H1.
rewrite <- H9 in H2.
rewrite <- H6 in y3.
exact (H0 _ _ _ y3 H2).
rewrite y2 in H1.
inversion H1.
rewrite <- H6 in H1.
exact (H0 _ _ _ H1 H2).
rewrite y in H1.
rewrite <- H6 in H1.
exact (H0 _ _ _ H1 H2).
intros.
simpl in H.
inversion H.
rewrite <- H2 in H0.
inversion H0.
