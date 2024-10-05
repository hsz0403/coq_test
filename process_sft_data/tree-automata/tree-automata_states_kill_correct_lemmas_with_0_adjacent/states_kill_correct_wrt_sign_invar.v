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

Lemma states_kill_correct_wrt_sign_invar : forall (s s' : state) (m : Map bool) (sigma : signature), state_correct_wrt_sign s sigma -> states_kill m s = Some s' -> state_correct_wrt_sign s' sigma.
Proof.
unfold states_kill in |- *.
intros.
elim (map_sum prec_list (states_kill_aux m s)); intros.
rewrite H1 in H0.
inversion H0.
elim H1; intros; elim H2; intros; elim H3; intros; rewrite H4 in H0.
inversion H0.
rewrite <- H4.
exact (states_kill_aux_correct_wrt_sign_invar _ _ _ H).
inversion H0.
rewrite <- H4.
exact (states_kill_aux_correct_wrt_sign_invar _ _ _ H).
