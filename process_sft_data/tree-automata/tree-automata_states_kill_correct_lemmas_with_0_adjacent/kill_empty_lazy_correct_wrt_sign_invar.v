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

Lemma kill_empty_lazy_correct_wrt_sign_invar : forall (d : DTA) (sigma : signature), dta_correct_wrt_sign d sigma -> dta_correct_wrt_sign (DTA_kill_empty_states_lazy d) sigma.
Proof.
intro.
rewrite (kill_empty_states_lazy_eg_kill_empty_states d).
exact (kill_empty_correct_wrt_sign_invar d).
