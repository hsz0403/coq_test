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

Lemma prec_list_kill_ref_ok_invar : forall (d : preDTA) (p p' : prec_list) (sigma : signature), prec_list_ref_ok p d -> predta_correct_wrt_sign d sigma -> prec_list_kill (dta_non_empty_states d) p = Some p' -> prec_list_ref_ok p' (preDTA_kill (dta_non_empty_states d) d).
Proof.
intros.
unfold prec_list_ref_ok in |- *.
intros.
elim (dt_non_empty_fix d a).
intros.
elim (H3 (prec_list_kill_occur _ _ _ _ H1 H2)).
intros.
elim (dt_kill_empty_kill_empty d a sigma H0).
intros.
apply H7.
split with x.
exact H5.
