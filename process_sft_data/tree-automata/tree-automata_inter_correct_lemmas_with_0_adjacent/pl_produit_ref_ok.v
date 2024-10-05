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

Lemma pl_produit_ref_ok : forall (p0 p1 : prec_list) (d0 d1 : preDTA), prec_list_ref_ok p0 d0 -> prec_list_ref_ok p1 d1 -> prec_list_ref_ok (pl_produit p0 p1) (preDTA_produit d0 d1).
Proof.
unfold prec_list_ref_ok in |- *.
intros.
elim (pl_produit_ref_ok_lem_6 p0 p1 a H1).
intros.
elim H2.
intros.
elim H3.
intros.
elim H5.
intros.
elim (H _ H6).
elim (H0 _ H7).
intros.
rewrite H4.
split with (s_produit x2 x1).
exact (predta_produit_2 d0 d1 x x0 x2 x1 H9 H8).
