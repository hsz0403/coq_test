Require Import Bool.
Require Import Arith.
Require Import ZArith.
From IntMap Require Import Allmaps.
Require Import bases.
Require Import defs.
Require Import semantics.
Require Import refcorrect.
Require Import signature.
Require Import lattice_fixpoint.
Require Import coacc_test.
Require Import non_coacc_kill.

Lemma predta_kill_non_coacc_correct_wrt_sign : forall (d : preDTA) (a : ad) (sigma : signature), preDTA_ref_ok d -> predta_correct_wrt_sign d sigma -> predta_correct_wrt_sign (predta_kill_non_coacc d a) sigma.
Proof.
unfold predta_correct_wrt_sign in |- *.
intros.
elim (predta_kill_non_coacc_0 d a a0 s H).
intros.
elim (H3 H1).
intros.
Admitted.

Lemma dta_kill_non_coacc_correct_wrt_sign : forall (d : DTA) (sigma : signature), DTA_ref_ok d -> dta_correct_wrt_sign d sigma -> dta_correct_wrt_sign (dta_kill_non_coacc d) sigma.
Proof.
simple induction d.
simpl in |- *.
Admitted.

Lemma dta_kill_non_coacc_lazy_correct_wrt_sign : forall (d : DTA) (sigma : signature), DTA_ref_ok d -> dta_correct_wrt_sign d sigma -> dta_correct_wrt_sign (dta_kill_non_coacc_lazy d) sigma.
Proof.
intros.
rewrite (kill_non_coacc_lazy_eq_kill_non_coacc d).
Admitted.

Lemma predta_kill_non_coacc_correct_ref_ok : forall (d : preDTA) (a : ad), preDTA_ref_ok d -> preDTA_ref_ok (predta_kill_non_coacc d a).
Proof.
unfold preDTA_ref_ok in |- *.
intros.
elim (predta_kill_non_coacc_0 d a a0 s H).
intros.
elim (H4 H0).
intros.
elim (H a0 s c pl b H5 H1 H2).
intros.
split with x.
elim (predta_kill_non_coacc_0 d a b x H).
intros.
apply H8.
split.
exact H7.
Admitted.

Lemma dta_kill_non_coacc_correct_ref_ok : forall d : DTA, DTA_ref_ok d -> DTA_ref_ok (dta_kill_non_coacc d).
Proof.
simple induction d.
simpl in |- *.
Admitted.

Lemma dta_kill_non_coacc_lazy_correct_ref_ok : forall d : DTA, DTA_ref_ok d -> DTA_ref_ok (dta_kill_non_coacc_lazy d).
Proof.
intros.
rewrite (kill_non_coacc_lazy_eq_kill_non_coacc d).
Admitted.

Lemma dta_kill_non_coacc_correct_main_state : forall d : DTA, DTA_ref_ok d -> DTA_main_state_correct d -> DTA_main_state_correct (dta_kill_non_coacc d).
Proof.
simple induction d.
simpl in |- *.
unfold addr_in_preDTA in |- *.
intros.
elim H0.
intros.
elim (predta_kill_non_coacc_0 p a a x H).
intros.
split with x.
apply H2.
split.
exact H1.
Admitted.

Lemma dta_kill_non_coacc_lazy_correct_main_state : forall d : DTA, DTA_ref_ok d -> DTA_main_state_correct d -> DTA_main_state_correct (dta_kill_non_coacc_lazy d).
Proof.
intros.
rewrite (kill_non_coacc_lazy_eq_kill_non_coacc d).
exact (dta_kill_non_coacc_correct_main_state d H H0).
