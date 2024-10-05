Require Import Bool.
Require Import NArith Ndec Ndigits.
Require Import ZArith.
Require Import Classical_Prop.
From IntMap Require Import Allmaps.
Require Import bases.
Require Import defs.
Require Import semantics.
Require Import signature.
Require Import refcorrect.
Require Import union.

Lemma insert_ostate_correct_wrt_sign_invar : forall (d : preDTA) (a : ad) (s : state) (sigma : signature), predta_correct_wrt_sign d sigma -> state_correct_wrt_sign s sigma -> predta_correct_wrt_sign (insert_ostate d a (Some s)) sigma.
Proof.
unfold predta_correct_wrt_sign in |- *.
unfold insert_ostate in |- *.
intros.
rewrite (MapPut_semantics state d a s) in H1.
elim (bool_is_true_or_false (N.eqb a a0)); intros; rewrite H2 in H1.
inversion H1.
rewrite <- H4.
exact H0.
exact (H a0 s0 H1).
