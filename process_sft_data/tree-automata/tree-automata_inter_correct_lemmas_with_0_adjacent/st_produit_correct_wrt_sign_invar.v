Require Import Bool.
Require Import NArith Ndec Ndigits.
Require Import ZArith.
From IntMap Require Import Allmaps.
Require Import bases.
Require Import defs.
Require Import semantics.
Require Import signature.
Require Import refcorrect.
Require Import inter.
Definition pl_produit_ref_ok_0 (la pl : prec_list) : Prop := forall (a b : ad) (l : prec_list) (n : nat), prec_occur (pl_produit_0 a la pl n l) b -> (exists a0 : ad, (exists a1 : ad, b = iad_conv a0 a1 /\ prec_occur la a0 /\ prec_occur pl a1)) \/ (exists a1 : ad, b = iad_conv a a1 /\ prec_occur pl a1) \/ prec_occur l b.
Definition pl_produit_ref_ok_1 (p0 p1 : prec_list) : Prop := forall (b : ad) (n : nat), prec_occur (pl_produit_1 p0 n p1) b -> exists a0 : ad, (exists a1 : ad, b = iad_conv a0 a1 /\ prec_occur p0 a0 /\ prec_occur p1 a1).

Lemma st_produit_correct_wrt_sign_invar : forall (s0 s1 : state) (sigma : signature), state_correct_wrt_sign s0 sigma -> state_correct_wrt_sign s1 sigma -> state_correct_wrt_sign (s_produit s0 s1) sigma.
Proof.
intros.
replace (state_correct_wrt_sign (s_produit s0 s1) sigma) with (state_correct_wrt_sign_with_offset (s_produit s0 s1) sigma pre_ad_empty).
apply (st_produit_correct_wrt_sign_invar_with_offset s0 s1 sigma pre_ad_empty).
unfold state_correct_wrt_sign_with_offset in |- *.
simpl in |- *.
exact H.
unfold state_correct_wrt_sign_with_offset in |- *.
simpl in |- *.
exact H0.
reflexivity.
