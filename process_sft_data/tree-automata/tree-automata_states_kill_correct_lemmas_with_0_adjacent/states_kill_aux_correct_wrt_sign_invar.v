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

Lemma states_kill_aux_correct_wrt_sign_invar : forall (s : state) (m : Map bool) (sigma : signature), state_correct_wrt_sign s sigma -> state_correct_wrt_sign (states_kill_aux m s) sigma.
Proof.
unfold state_correct_wrt_sign in |- *.
intros.
elim (st_kill_2 _ _ _ _ H0).
intros.
elim H1.
intros.
elim (H _ _ H2).
intros.
split with x0.
elim H4.
intros.
split.
exact H5.
exact (prec_list_kill_correct_wrt_sign_invar _ _ _ _ H6 H3).
