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

Lemma preDTA_produit_ref_okd : forall d0 d1 d0' d1' : preDTA, preDTA_ref_ok_distinct d0 d0' -> preDTA_ref_ok_distinct d1 d1' -> preDTA_ref_ok_distinct (preDTA_produit d0 d1) (preDTA_produit d0' d1').
Proof.
simple induction d0.
simple induction d1.
simpl in |- *.
intros.
unfold preDTA_ref_ok_distinct in |- *.
intros.
inversion H1.
simpl in |- *.
intros.
unfold preDTA_ref_ok_distinct in |- *.
intros.
inversion H1.
intros.
simpl in |- *.
unfold preDTA_ref_ok_distinct in |- *.
intros.
inversion H3.
simple induction d1.
simpl in |- *.
intros.
unfold preDTA_ref_ok_distinct in |- *.
intros.
inversion H1.
intros.
replace (preDTA_produit (M1 state a a0) (M1 state a1 a2)) with (preDTA_produit_l a a0 (M1 state a1 a2)).
exact (preDTA_produit_l_ref_ok _ _ _ _ _ H0 H).
reflexivity.
intros.
replace (preDTA_produit (M1 state a a0) (M2 state m m0)) with (preDTA_produit_l a a0 (M2 state m m0)).
exact (preDTA_produit_l_ref_ok _ _ _ _ _ H2 H1).
reflexivity.
simple induction d1.
intros.
simpl in |- *.
unfold preDTA_ref_ok_distinct in |- *.
intros.
inversion H3.
intros.
replace (preDTA_produit (M2 state m m0) (M1 state a a0)) with (preDTA_produit_r a a0 (M2 state m m0)).
exact (preDTA_produit_r_ref_ok _ _ _ _ _ H1 H2).
reflexivity.
intros.
elim (preDTA_ref_ok_distinct_dest _ _ _ H3).
elim (preDTA_ref_ok_distinct_dest _ _ _ H4).
intros.
simpl in |- *.
unfold preDTA_ref_ok_distinct in |- *.
intros.
induction a as [| p].
simpl in H9.
exact (H _ _ _ H7 H5 _ _ H9).
induction p as [p Hrecp| p Hrecp| ].
simpl in H9.
elim (positive_sum p); intros.
rewrite H10 in H9.
exact (H0 _ _ _ H8 H6 _ _ H9).
elim H10; intros; elim H11; intros; rewrite H12 in H9.
exact (H0 _ _ _ H8 H5 _ _ H9).
exact (H0 _ _ _ H8 H6 _ _ H9).
simpl in H9.
elim (positive_sum p); intros.
rewrite H10 in H9.
exact (H _ _ _ H7 H6 _ _ H9).
elim H10; intros; elim H11; intros; rewrite H12 in H9.
exact (H _ _ _ H7 H5 _ _ H9).
exact (H _ _ _ H7 H6 _ _ H9).
simpl in H9.
exact (H0 _ _ _ H8 H5 _ _ H9).
