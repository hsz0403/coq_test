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
exact (coacc_id p a x H1).
