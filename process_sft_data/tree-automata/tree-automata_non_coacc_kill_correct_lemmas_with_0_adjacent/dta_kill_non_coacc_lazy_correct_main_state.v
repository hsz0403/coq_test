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

Lemma dta_kill_non_coacc_lazy_correct_main_state : forall d : DTA, DTA_ref_ok d -> DTA_main_state_correct d -> DTA_main_state_correct (dta_kill_non_coacc_lazy d).
Proof.
intros.
rewrite (kill_non_coacc_lazy_eq_kill_non_coacc d).
exact (dta_kill_non_coacc_correct_main_state d H H0).
