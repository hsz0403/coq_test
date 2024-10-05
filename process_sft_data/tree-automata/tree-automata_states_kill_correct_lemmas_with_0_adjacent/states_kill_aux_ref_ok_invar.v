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

Lemma states_kill_aux_ref_ok_invar : forall (d : preDTA) (s : state) (sigma : signature), state_ref_ok s d -> predta_correct_wrt_sign d sigma -> state_ref_ok (states_kill_aux (dta_non_empty_states d) s) (preDTA_kill (dta_non_empty_states d) d).
Proof.
unfold state_ref_ok in |- *.
intros.
elim (st_kill_2 _ _ _ _ H1).
intros.
elim H2.
intros.
exact (prec_list_kill_ref_ok_invar d x p sigma (H a x H3) H0 H4).
