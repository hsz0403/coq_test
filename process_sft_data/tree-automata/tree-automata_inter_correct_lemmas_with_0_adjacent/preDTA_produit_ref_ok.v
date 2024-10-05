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

Lemma preDTA_produit_ref_ok : forall d0 d1 : preDTA, preDTA_ref_ok d0 -> preDTA_ref_ok d1 -> preDTA_ref_ok (preDTA_produit d0 d1).
Proof.
intros.
cut (preDTA_ref_ok_distinct (preDTA_produit d0 d1) (preDTA_produit d0 d1)).
intro.
unfold preDTA_ref_ok_distinct in H1.
elim (preDTA_ref_ok_def (preDTA_produit d0 d1)).
intros.
exact (H3 H1).
apply (preDTA_produit_ref_okd d0 d1 d0 d1).
unfold preDTA_ref_ok_distinct in |- *.
elim (preDTA_ref_ok_def d0).
intros.
exact (H1 H _ _ H3).
elim (preDTA_ref_ok_def d1); intros.
exact (H1 H0).
