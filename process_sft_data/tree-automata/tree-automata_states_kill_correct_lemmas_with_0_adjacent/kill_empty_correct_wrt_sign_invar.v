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

Lemma kill_empty_correct_wrt_sign_invar : forall (d : DTA) (sigma : signature), dta_correct_wrt_sign d sigma -> dta_correct_wrt_sign (DTA_kill_empty_states d) sigma.
Proof.
simple induction d.
simpl in |- *.
intros.
elim (option_sum state (MapGet state (preDTA_kill (dta_non_empty_states p) p) a)); intros y.
elim y.
intros x y0.
rewrite y0.
simpl in |- *.
exact (kill_empty_correct_wrt_sign_invar p sigma (dta_non_empty_states p) H).
rewrite y.
simpl in |- *.
unfold predta_correct_wrt_sign in |- *.
intros.
simpl in H0.
elim (N.discr a0).
intros y0.
elim y0.
intros x y1.
rewrite y1 in H0.
inversion H0.
intros y0.
rewrite y0 in H0.
inversion H0.
unfold state_correct_wrt_sign in |- *.
intros.
inversion H1.
