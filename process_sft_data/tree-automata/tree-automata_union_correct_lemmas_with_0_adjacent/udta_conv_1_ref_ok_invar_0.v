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

Lemma udta_conv_1_ref_ok_invar_0 : forall (d : preDTA) (a : ad) (s : state) (c : ad) (p : prec_list) (b : ad), MapGet state (udta_conv_1 d) (uad_conv_1 a) = Some s -> MapGet prec_list s c = Some p -> prec_occur p b -> exists s' : state, (exists p' : prec_list, (exists b' : ad, MapGet state d a = Some s' /\ MapGet prec_list s' c = Some p' /\ p = upl_conv_1 p' /\ s = umpl_conv_1 s' /\ b = uad_conv_1 b' /\ prec_occur p' b')).
Proof.
intros.
elim (u_conv_1_invar_5 d a s H).
intros.
split with x.
elim H2.
intros.
rewrite H3 in H0.
elim (u_conv_1_invar_7 x c p H0).
intros.
split with x0.
elim H5.
intros.
rewrite H6 in H1.
elim (upl_conv_1_ref_ok_invar x0 b H1).
intros.
split with x1.
elim H8.
intros.
split.
exact H4.
split.
exact H7.
split.
exact H6.
split.
exact H3.
split.
exact H9.
exact H10.
