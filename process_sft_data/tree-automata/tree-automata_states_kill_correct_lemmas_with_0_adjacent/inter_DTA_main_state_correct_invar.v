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

Lemma inter_DTA_main_state_correct_invar : forall d : DTA, DTA_main_state_correct d -> DTA_main_state_correct (DTA_kill (dta_states_non_empty d) d).
Proof.
simple induction d.
simpl in |- *.
intros.
elim (option_sum state (MapGet state (preDTA_kill (dta_non_empty_states p) p) a)); intros y.
elim y.
intros x y0.
rewrite y0.
simpl in |- *.
unfold addr_in_preDTA in |- *.
unfold addr_in_preDTA in H.
split with x.
exact y0.
rewrite y.
simpl in |- *.
unfold addr_in_preDTA in |- *.
intros.
split with (M0 prec_list).
reflexivity.
