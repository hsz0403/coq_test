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

Lemma u_merge_ref_ok_invar : forall d0 d1 : preDTA, preDTA_ref_ok d0 -> preDTA_ref_ok d1 -> preDTA_ref_ok (u_merge d0 d1).
Proof.
unfold u_merge in |- *.
exact (fun (d0 d1 : preDTA) (p0 : preDTA_ref_ok d0) (p1 : preDTA_ref_ok d1) => MapMerge_ref_ok_invar (udta_conv_0 d0) (udta_conv_1 d1) (udta_conv_0_ref_ok_invar d0 p0) (udta_conv_1_ref_ok_invar d1 p1)).
