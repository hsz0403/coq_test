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

Lemma union_correct_wrt_sign_invar : forall (d0 d1 : DTA) (sigma : signature), dta_correct_wrt_sign d0 sigma -> dta_correct_wrt_sign d1 sigma -> dta_correct_wrt_sign (union d0 d1) sigma.
Proof.
unfold union in |- *.
simple induction d0.
simple induction d1.
unfold union_1 in |- *.
unfold insert_main_ostate in |- *.
unfold dta_correct_wrt_sign in |- *.
intros.
unfold insert_main_ostate_0 in |- *.
elim (option_sum state (union_0 (u_merge p p0) a a0)).
intros y.
elim y.
intros x y0.
rewrite y0.
exact (insert_ostate_correct_wrt_sign_invar (u_merge p p0) (new_preDTA_ad (u_merge p p0)) x sigma (umerge_correct_wrt_sign_invar _ _ _ H H0) (union_0_correct_wrt_sign_invar (u_merge p p0) a a0 x sigma (umerge_correct_wrt_sign_invar _ _ _ H H0) y0)).
intro y.
rewrite y.
simpl in |- *.
exact (umerge_correct_wrt_sign_invar _ _ _ H H0).
