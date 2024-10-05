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

Lemma preDTA_kill_ref_ok_invar : forall (d : preDTA) (sigma : signature), preDTA_ref_ok d -> predta_correct_wrt_sign d sigma -> preDTA_ref_ok (preDTA_kill (dta_non_empty_states d) d).
Proof.
intros.
elim (preDTA_ref_ok_def (preDTA_kill (dta_non_empty_states d) d)).
intros.
apply H2.
elim (preDTA_ref_ok_def d).
intro.
intro.
exact (preDTA_kill_ref_ok_distinct_invar d sigma (H3 H) H0).
