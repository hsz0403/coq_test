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

Lemma udta_conv_0_correct_wrt_sign_invar : forall (d : preDTA) (sigma : signature), predta_correct_wrt_sign d sigma -> predta_correct_wrt_sign (udta_conv_0 d) sigma.
Proof.
unfold udta_conv_0 in |- *.
intros.
unfold predta_correct_wrt_sign in |- *.
intros.
induction a as [| p].
simpl in H0.
exact (udta_conv_0_correct_wrt_sign_invar_0 d sigma H N0 s H0).
induction p as [p Hrecp| p Hrecp| ]; simpl in H0.
inversion H0.
exact (udta_conv_0_correct_wrt_sign_invar_0 d sigma H (Npos p) s H0).
inversion H0.
