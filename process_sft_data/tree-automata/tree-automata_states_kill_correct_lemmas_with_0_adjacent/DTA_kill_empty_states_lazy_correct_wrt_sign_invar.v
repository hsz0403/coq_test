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

Lemma DTA_kill_empty_states_lazy_correct_wrt_sign_invar : forall (d : DTA) (sigma : signature), dta_correct_wrt_sign d sigma -> dta_correct_wrt_sign (DTA_kill_empty_states_lazy d) sigma.
Proof.
intro.
rewrite (kill_empty_states_lazy_eg_kill_empty_states d).
unfold DTA_kill_empty_states in |- *.
exact (DTA_kill_correct_wrt_sign_invar d (dta_states_non_empty d)).
