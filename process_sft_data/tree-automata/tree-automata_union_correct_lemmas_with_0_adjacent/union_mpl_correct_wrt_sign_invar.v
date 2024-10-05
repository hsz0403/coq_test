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

Lemma union_mpl_correct_wrt_sign_invar : forall (s0 s1 : state) (sigma : signature), state_correct_wrt_sign s0 sigma -> state_correct_wrt_sign s1 sigma -> state_correct_wrt_sign (union_mpl s0 s1) sigma.
Proof.
intros.
replace (state_correct_wrt_sign (union_mpl s0 s1) sigma) with (state_correct_wrt_sign_with_offset (union_mpl s0 s1) sigma pre_ad_empty).
apply (union_mpl_correct_wrt_sign_invar_1 s0 s1 pre_ad_empty sigma).
unfold state_correct_wrt_sign_with_offset in |- *.
simpl in |- *.
exact H.
unfold state_correct_wrt_sign_with_offset in |- *.
simpl in |- *.
exact H0.
unfold state_correct_wrt_sign_with_offset in |- *.
reflexivity.
