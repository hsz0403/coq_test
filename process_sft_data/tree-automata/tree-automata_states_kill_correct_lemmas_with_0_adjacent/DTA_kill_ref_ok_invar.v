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

Lemma DTA_kill_ref_ok_invar : forall (d : DTA) (sigma : signature), DTA_ref_ok d -> dta_correct_wrt_sign d sigma -> DTA_ref_ok (DTA_kill (dta_states_non_empty d) d).
Proof.
simple induction d.
simpl in |- *.
intros.
elim (option_sum state (MapGet state (preDTA_kill (dta_non_empty_states p) p) a)); intros y.
elim y.
intros x y0.
rewrite y0.
exact (preDTA_kill_ref_ok_invar _ _ H H0).
rewrite y.
simpl in |- *.
unfold preDTA_ref_ok in |- *.
intros.
simpl in H1.
elim (N.discr a0); intros y0.
elim y0.
intros x y1.
rewrite y1 in H1.
inversion H1.
rewrite y0 in H1.
inversion H1.
rewrite <- H5 in H2.
inversion H2.
