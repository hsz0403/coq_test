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

Lemma s_produit_r_ref_ok : forall (s : state) (a : ad) (p : prec_list) (d0 d1 : preDTA), state_ref_ok s d1 -> state_ref_ok (M1 prec_list a p) d0 -> state_ref_ok (s_produit_r a p s) (preDTA_produit d1 d0).
Proof.
simple induction s.
simpl in |- *.
unfold state_ref_ok in |- *.
intros.
inversion H1.
simpl in |- *.
unfold state_ref_ok in |- *.
intros.
elim (bool_is_true_or_false (N.eqb a1 a)); intros.
rewrite H2 in H1.
simpl in H1.
elim (bool_is_true_or_false (N.eqb a1 a2)); intros; rewrite H3 in H1; inversion H1.
apply (pl_produit_ref_ok a0 p d1 d0).
apply (H a a0).
simpl in |- *.
rewrite (Neqb_correct a).
reflexivity.
apply (H0 a1 p).
simpl in |- *.
rewrite (Neqb_correct a1).
reflexivity.
rewrite H2 in H1.
inversion H1.
intro.
intro.
intro.
intro.
unfold state_ref_ok in |- *.
intros.
cut (forall a : ad, state_ref_ok (M1 prec_list a p) d0).
intro.
elim (state_ref_ok_M2_destr _ _ _ H1).
intros.
simpl in H3.
induction a as [| p1].
simpl in H3.
induction a0 as [| p1].
exact (H _ _ _ _ H5 (H4 N0) _ _ H3).
elim (positive_sum p1).
intros.
rewrite H7 in H3.
inversion H3.
intros.
elim H7; intros; elim H8; intros; rewrite H9 in H3.
exact (H _ _ _ _ H5 (H4 N0) _ _ H3).
inversion H3.
elim (positive_sum p1); intros.
rewrite H7 in H3.
simpl in H3.
induction a0 as [| p2].
inversion H3.
elim (positive_sum p2); intros.
rewrite H8 in H3.
exact (H0 _ _ _ _ H6 (H4 N0) _ _ H3).
elim H8; intros; elim H9; intros; rewrite H10 in H3.
inversion H3.
exact (H0 _ _ _ _ H6 (H4 N0) _ _ H3).
elim H7; intros; elim H8; intros; rewrite H9 in H3.
simpl in H3.
induction a0 as [| p2].
exact (H _ _ _ _ H5 (H4 (Npos x)) _ _ H3).
elim (positive_sum p2); intros.
rewrite H10 in H3.
inversion H3.
elim H10; intros; elim H11; intros; rewrite H12 in H3.
exact (H _ _ _ _ H5 (H4 (Npos x)) _ _ H3).
inversion H3.
simpl in H3.
induction a0 as [| p2].
inversion H3.
elim (positive_sum p2); intros.
rewrite H10 in H3.
exact (H0 _ _ _ _ H6 (H4 (Npos x)) _ _ H3).
elim H10; intros; elim H11; intros; rewrite H12 in H3.
inversion H3.
exact (H0 _ _ _ _ H6 (H4 (Npos x)) _ _ H3).
unfold state_ref_ok in |- *.
intros.
simpl in H4.
elim (bool_is_true_or_false (N.eqb a1 a2)); intros; rewrite H5 in H4.
inversion H4.
rewrite <- H7.
apply (H2 a p).
simpl in |- *.
rewrite (Neqb_correct a).
reflexivity.
inversion H4.
