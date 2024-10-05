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

Lemma umpl_conv_0_correct_wrt_sign_invar : forall (s : state) (sigma : signature), state_correct_wrt_sign s sigma -> state_correct_wrt_sign (umpl_conv_0 s) sigma.
Proof.
unfold state_correct_wrt_sign in |- *.
intros.
elim (umpl_conv_0_correct_wrt_sign_invar_0 s sigma pre_ad_empty) with (a := a) (p := p).
intros.
split with x.
simpl in H1.
exact H1.
unfold state_correct_wrt_sign_with_offset in |- *.
simpl in |- *.
exact H.
exact H0.
