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

Lemma DTA_kill_ref_ok_invar_lazy : forall (d : DTA) (sigma : signature), DTA_ref_ok d -> dta_correct_wrt_sign d sigma -> DTA_ref_ok (DTA_kill_empty_states_lazy d).
Proof.
intro.
rewrite (kill_empty_states_lazy_eg_kill_empty_states d).
exact (DTA_kill_ref_ok_invar d).
