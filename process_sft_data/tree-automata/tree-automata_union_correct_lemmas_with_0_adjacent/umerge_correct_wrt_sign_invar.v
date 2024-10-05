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

Lemma umerge_correct_wrt_sign_invar : forall (d0 d1 : preDTA) (sigma : signature), predta_correct_wrt_sign d0 sigma -> predta_correct_wrt_sign d1 sigma -> predta_correct_wrt_sign (u_merge d0 d1) sigma.
Proof.
unfold predta_correct_wrt_sign in |- *.
intros.
elim (adcnv_disj a).
intros.
elim H2; intros.
elim (u_conv_0_invar_5 d0 x s).
intros.
elim H4.
intros.
apply (udta_conv_0_correct_wrt_sign_invar d0 sigma H a s).
exact (u_merge_0r d0 d1 a s H1 x H3).
rewrite <- H3.
exact (u_merge_0r d0 d1 a s H1 x H3).
elim (u_conv_1_invar_5 d1 x s).
intros.
elim H4.
intros.
apply (udta_conv_1_correct_wrt_sign_invar d1 sigma H0 a s).
exact (u_merge_1r d0 d1 a s H1 x H3).
rewrite <- H3.
exact (u_merge_1r d0 d1 a s H1 x H3).
