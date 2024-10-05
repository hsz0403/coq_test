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

Lemma udta_conv_1_ref_ok_invar : forall d : preDTA, preDTA_ref_ok d -> preDTA_ref_ok (udta_conv_1 d).
Proof.
unfold preDTA_ref_ok in |- *.
intros.
elim (u_conv_1_invar_8 _ _ _ H0).
intros.
rewrite H3 in H0.
elim (udta_conv_1_ref_ok_invar_0 _ _ _ _ _ _ H0 H1 H2).
intros.
elim H4.
intros.
elim H5.
intros.
decompose [and] H6.
elim (H _ _ _ _ _ H7 H9 H13).
intros.
split with (umpl_conv_1 x3).
rewrite H11.
exact (u_conv_1_invar_0 _ _ _ H12).
