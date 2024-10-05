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

Lemma prec_list_kill_correct_wrt_sign_invar : forall (m : Map bool) (p p' : prec_list) (n : nat), pl_tl_length p n -> prec_list_kill m p = Some p' -> pl_tl_length p' n.
Proof.
intros.
apply (forall_incl_length p' n).
intros.
elim (pl_kill_1 p p' m p0 H0 H1).
intros.
exact (pl_path_incl_length p0 p n H2 H).
