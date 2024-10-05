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

Lemma preDTA_kill_ref_ok_distinct_invar : forall (d : preDTA) (sigma : signature), preDTA_ref_ok_distinct d d -> predta_correct_wrt_sign d sigma -> preDTA_ref_ok_distinct (preDTA_kill (dta_non_empty_states d) d) (preDTA_kill (dta_non_empty_states d) d).
Proof.
unfold preDTA_ref_ok_distinct in |- *.
intros.
elim (dt_kill_1 _ _ _ _ H1).
intros.
elim H2.
intros.
exact (states_kill_ref_ok_invar d x s sigma (H a x H3) H0 H4).
