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

Lemma st_produit_correct_wrt_sign_invar_with_offset : forall (s0 s1 : state) (sigma : signature) (pa : pre_ad), state_correct_wrt_sign_with_offset s0 sigma pa -> state_correct_wrt_sign_with_offset s1 sigma pa -> state_correct_wrt_sign_with_offset (s_produit s0 s1) sigma pa.
Proof.
simple induction s0.
simple induction s1.
intros.
simpl in |- *.
unfold state_correct_wrt_sign_with_offset in |- *.
intros.
inversion H1.
intros.
simpl in |- *.
unfold state_correct_wrt_sign_with_offset in |- *.
intros.
inversion H1.
intros.
simpl in |- *.
unfold state_correct_wrt_sign_with_offset in |- *.
intros.
inversion H3.
simple induction s1.
simpl in |- *.
intros.
unfold state_correct_wrt_sign_with_offset in |- *.
intros.
inversion H1.
intros.
replace (s_produit (M1 prec_list a a0) (M1 prec_list a1 a2)) with (s_produit_l a a0 (M1 prec_list a1 a2)).
exact (st_produit_l_correct_wrt_sign_invar_with_offset (M1 prec_list a1 a2) a a0 sigma pa H0 H).
reflexivity.
intros.
replace (s_produit (M1 prec_list a a0) (M2 prec_list m m0)) with (s_produit_l a a0 (M2 prec_list m m0)).
exact (st_produit_l_correct_wrt_sign_invar_with_offset (M2 prec_list m m0) a a0 sigma pa H2 H1).
reflexivity.
simple induction s1.
simpl in |- *.
intros.
exact H2.
intros.
replace (s_produit (M2 prec_list m m0) (M1 prec_list a a0)) with (s_produit_r a a0 (M2 prec_list m m0)).
exact (st_produit_r_correct_wrt_sign_invar_with_offset (M2 prec_list m m0) a a0 sigma pa H1 H2).
reflexivity.
intros.
unfold state_correct_wrt_sign_with_offset in |- *.
simpl in |- *.
intros.
elim (state_correct_wrt_sign_with_offset_M2 _ _ _ _ H3).
intros.
elim (state_correct_wrt_sign_with_offset_M2 _ _ _ _ H4).
intros.
induction a as [| p0].
exact (H _ _ _ H6 H8 N0 p H5).
induction p0 as [p0 Hrecp0| p0 Hrecp0| ].
exact (H0 _ _ _ H7 H9 (Npos p0) p H5).
exact (H _ _ _ H6 H8 _ _ H5).
exact (H0 _ _ _ H7 H9 _ _ H5).
