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

Lemma preDTA_kill_correct_wrt_sign_invar : forall (d : preDTA) (m : Map bool) (sigma : signature), predta_correct_wrt_sign d sigma -> predta_correct_wrt_sign (preDTA_kill m d) sigma.
Proof.
unfold predta_correct_wrt_sign in |- *.
intros.
elim (dt_kill_1 _ _ _ _ H0).
intros.
elim H1.
intros.
exact (states_kill_correct_wrt_sign_invar _ _ _ _ (H _ _ H2) H3).
