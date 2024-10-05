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

Lemma preDTA_produit_correct_wrt_sign_invar : forall (d0 d1 : preDTA) (sigma : signature), predta_correct_wrt_sign d0 sigma -> predta_correct_wrt_sign d1 sigma -> predta_correct_wrt_sign (preDTA_produit d0 d1) sigma.
Proof.
simple induction d0.
simple induction d1.
simpl in |- *.
intros.
exact H.
simpl in |- *.
intros.
exact H.
intros.
simpl in |- *.
exact H1.
simple induction d1.
simpl in |- *.
intros.
exact H0.
intros.
replace (preDTA_produit (M1 state a a0) (M1 state a1 a2)) with (preDTA_produit_l a a0 (M1 state a1 a2)).
exact (preDTA_produit_l_correct_wrt_sign_invar (M1 state a1 a2) a a0 sigma H0 H).
reflexivity.
intros.
replace (preDTA_produit (M1 state a a0) (M2 state m m0)) with (preDTA_produit_l a a0 (M2 state m m0)).
exact (preDTA_produit_l_correct_wrt_sign_invar (M2 state m m0) a a0 sigma H2 H1).
reflexivity.
simple induction d1.
simpl in |- *.
intros.
exact H2.
intros.
replace (preDTA_produit (M2 state m m0) (M1 state a a0)) with (preDTA_produit_r a a0 (M2 state m m0)).
exact (preDTA_produit_r_correct_wrt_sign_invar (M2 state m m0) a a0 sigma H1 H2).
reflexivity.
intros.
simpl in |- *.
elim (predta_correct_wrt_sign_M2 _ _ _ H3).
intros.
elim (predta_correct_wrt_sign_M2 _ _ _ H4).
intros.
unfold predta_correct_wrt_sign in |- *.
intros.
simpl in H9.
induction a as [| p].
exact (H _ _ H5 H7 N0 s H9).
elim (positive_sum p); intros.
rewrite H10 in H9.
exact (H0 _ _ H6 H7 _ _ H9).
elim H10; intros; elim H11; intros; rewrite H12 in H9.
elim (positive_sum x); intros.
rewrite H13 in H9.
exact (H _ _ H5 H8 _ _ H9).
elim H13; intros; elim H14; intros; rewrite H15 in H9.
exact (H _ _ H5 H7 _ _ H9).
exact (H _ _ H5 H8 _ _ H9).
elim (positive_sum x); intros.
rewrite H13 in H9.
exact (H0 _ _ H6 H8 _ _ H9).
elim H13; intros; elim H14; intros; rewrite H15 in H9.
exact (H0 _ _ H6 H7 _ _ H9).
exact (H0 _ _ H6 H8 _ _ H9).
