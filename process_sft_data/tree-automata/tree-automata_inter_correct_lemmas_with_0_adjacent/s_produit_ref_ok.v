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

Lemma s_produit_ref_ok : forall (s0 s1 : state) (d0 d1 : preDTA), state_ref_ok s0 d0 -> state_ref_ok s1 d1 -> state_ref_ok (s_produit s0 s1) (preDTA_produit d0 d1).
Proof.
simple induction s0.
simple induction s1.
intros.
simpl in |- *.
exact (st_M0_ref_ok (preDTA_produit d0 d1)).
intros.
simpl in |- *.
exact (st_M0_ref_ok (preDTA_produit d0 d1)).
intros.
simpl in |- *.
exact (st_M0_ref_ok (preDTA_produit d0 d1)).
simple induction s1.
intros.
simpl in |- *.
exact (st_M0_ref_ok (preDTA_produit d0 d1)).
intros.
replace (s_produit (M1 prec_list a a0) (M1 prec_list a1 a2)) with (s_produit_l a a0 (M1 prec_list a1 a2)).
exact (s_produit_l_ref_ok _ _ _ _ _ H0 H).
reflexivity.
intros.
replace (s_produit (M1 prec_list a a0) (M2 prec_list m m0)) with (s_produit_l a a0 (M2 prec_list m m0)).
exact (s_produit_l_ref_ok _ _ _ _ _ H2 H1).
reflexivity.
simple induction s1.
intros.
intros.
simpl in |- *.
exact (st_M0_ref_ok (preDTA_produit d0 d1)).
intros.
replace (s_produit (M2 prec_list m m0) (M1 prec_list a a0)) with (s_produit_r a a0 (M2 prec_list m m0)).
exact (s_produit_r_ref_ok _ _ _ _ _ H1 H2).
reflexivity.
intros.
simpl in |- *.
elim (state_ref_ok_M2_destr _ _ _ H3).
intros.
elim (state_ref_ok_M2_destr _ _ _ H4).
intros.
unfold state_ref_ok in |- *.
intros.
induction a as [| p0].
simpl in H9.
exact (H _ _ _ H5 H7 N0 p H9).
induction p0 as [p0 Hrecp0| p0 Hrecp0| ]; simpl in H9.
exact (H0 _ _ _ H6 H8 (Npos p0) p H9).
exact (H _ _ _ H5 H7 _ _ H9).
exact (H0 _ _ _ H6 H8 _ _ H9).
