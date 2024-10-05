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

Lemma inter_DTA_main_state_correct_invar_lazy : forall d : DTA, DTA_main_state_correct d -> DTA_main_state_correct (DTA_kill_empty_states_lazy d).
Proof.
intro.
rewrite (kill_empty_states_lazy_eg_kill_empty_states d).
exact (inter_DTA_main_state_correct_invar d).
