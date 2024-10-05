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

Lemma preDTA_produit_l_ref_ok : forall (d d0 d1 : preDTA) (s : state) (a : ad), preDTA_ref_ok_distinct d d1 -> preDTA_ref_ok_distinct (M1 state a s) d0 -> preDTA_ref_ok_distinct (preDTA_produit_l a s d) (preDTA_produit d0 d1).
Proof.
unfold preDTA_ref_ok_distinct in |- *.
simple induction d.
intros.
inversion H1.
intros.
simpl in H1.
elim (bool_is_true_or_false (N.eqb (iad_conv a1 a) a2)); intros; rewrite H2 in H1; inversion H1.
apply (s_produit_ref_ok s a0 d0 d1).
apply (H0 a1 s).
simpl in |- *.
rewrite (Neqb_correct a1).
reflexivity.
apply (H a a0).
simpl in |- *; rewrite (Neqb_correct a).
reflexivity.
intros.
elim (preDTA_ref_ok_distinct_dest m m0 d1 H1).
intros.
cut (forall a : ad, preDTA_ref_ok_distinct (M1 state a s) d0).
intros.
induction a as [| p].
simpl in H3.
induction a0 as [| p].
exact (H _ _ _ _ H4 (H6 N0) _ _ H3).
induction p as [p Hrecp| p Hrecp| ].
inversion H3.
elim (positive_sum p).
intros.
rewrite H7 in H3.
exact (H0 _ _ _ _ H5 (H6 N0) _ _ H3).
intros.
elim H7; intros; elim H8; intros; rewrite H9 in H3.
exact (H _ _ _ _ H4 (H6 N0) _ _ H3).
exact (H0 _ _ _ _ H5 (H6 N0) _ _ H3).
inversion H3.
induction p as [p Hrecp| p Hrecp| ].
induction a0 as [| p0].
simpl in H3.
inversion H3.
clear Hrecp.
induction p0 as [p0 Hrecp0| p0 Hrecp0| ]; simpl in H3.
elim (positive_sum p0); intros.
rewrite H7 in H3.
exact (H0 _ _ _ _ H5 (H6 (Npos p)) _ _ H3).
elim H7; intros; elim H8; intros; rewrite H9 in H3.
exact (H _ _ _ _ H4 (H6 (Npos p)) _ _ H3).
exact (H0 _ _ _ _ H5 (H6 (Npos p)) _ _ H3).
inversion H3.
exact (H _ _ _ _ H4 (H6 (Npos p)) _ _ H3).
induction a0 as [| p0].
simpl in H3.
exact (H _ _ _ _ H4 (H6 (Npos p)) _ _ H3).
induction p0 as [p0 Hrecp0| p0 Hrecp0| ]; simpl in H3.
inversion H3.
elim (positive_sum p0); intros.
rewrite H7 in H3.
exact (H0 _ _ _ _ H5 (H6 (Npos p)) _ _ H3).
elim H7; intros; elim H8; intros; rewrite H9 in H3.
exact (H _ _ _ _ H4 (H6 (Npos p)) _ _ H3).
exact (H0 _ _ _ _ H5 (H6 (Npos p)) _ _ H3).
inversion H3.
induction a0 as [| p].
simpl in H3.
inversion H3.
induction p as [p Hrecp| p Hrecp| ].
simpl in H3.
elim (positive_sum p); intros.
rewrite H7 in H3.
exact (H0 _ _ _ _ H5 (H6 N0) _ _ H3).
elim H7; intros; elim H8; intros; rewrite H9 in H3.
exact (H _ _ _ _ H4 (H6 N0) _ _ H3).
exact (H0 _ _ _ _ H5 (H6 N0) _ _ H3).
simpl in H3.
inversion H3.
simpl in H3.
exact (H _ _ _ _ H4 (H6 N0) _ _ H3).
unfold preDTA_ref_ok_distinct in |- *.
intros.
simpl in H6.
elim (bool_is_true_or_false (N.eqb a1 a2)); intros; rewrite H7 in H6; inversion H6.
rewrite <- H9.
apply (H2 a s).
simpl in |- *.
rewrite (Neqb_correct a).
reflexivity.
