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

Lemma DTA_kill_correct_wrt_sign_invar : forall (d : DTA) (m : Map bool) (sigma : signature), dta_correct_wrt_sign d sigma -> dta_correct_wrt_sign (DTA_kill m d) sigma.
Proof.
simple induction d.
simpl in |- *.
intros.
elim (option_sum state (MapGet state (preDTA_kill m p) a)).
intros y.
elim y.
intros x y0.
rewrite y0.
exact (preDTA_kill_correct_wrt_sign_invar _ _ _ H).
intros y.
rewrite y.
unfold dta_correct_wrt_sign in |- *.
unfold predta_correct_wrt_sign in |- *.
intros.
simpl in H0.
elim (N.discr a0); intros y0.
elim y0.
intros x y1.
rewrite y1 in H0.
inversion H0.
rewrite y0 in H0.
inversion H0.
unfold state_correct_wrt_sign in |- *.
intros.
inversion H1.
