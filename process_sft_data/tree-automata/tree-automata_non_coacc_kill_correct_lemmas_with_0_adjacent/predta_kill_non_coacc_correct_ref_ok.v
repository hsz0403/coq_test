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
exact (coacc_nxt d a a0 b s x pl c H7 H5 H1 H2 H6).
