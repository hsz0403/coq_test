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
exact (H0 _ _ H4).
