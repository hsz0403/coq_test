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

Lemma states_kill_ref_ok_invar : forall (d : preDTA) (s s' : state) (sigma : signature), state_ref_ok s d -> predta_correct_wrt_sign d sigma -> states_kill (dta_non_empty_states d) s = Some s' -> state_ref_ok s' (preDTA_kill (dta_non_empty_states d) d).
Proof.
intros.
unfold states_kill in H1.
elim (map_sum prec_list (states_kill_aux (dta_non_empty_states d) s)); intros.
rewrite H2 in H1.
inversion H1.
elim H2; intros; elim H3; intros; elim H4; intros; rewrite H5 in H1.
inversion H1.
rewrite <- H5.
exact (states_kill_aux_ref_ok_invar _ _ _ H H0).
inversion H1.
rewrite <- H5.
exact (states_kill_aux_ref_ok_invar _ _ _ H H0).
