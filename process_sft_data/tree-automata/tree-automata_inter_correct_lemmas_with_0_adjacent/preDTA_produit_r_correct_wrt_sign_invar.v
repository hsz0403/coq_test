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

Lemma preDTA_produit_r_correct_wrt_sign_invar : forall (d : preDTA) (a : ad) (s : state) (sigma : signature), predta_correct_wrt_sign d sigma -> predta_correct_wrt_sign (M1 state a s) sigma -> predta_correct_wrt_sign (preDTA_produit_r a s d) sigma.
Proof.
simple induction d.
intros.
simpl in |- *.
exact H.
unfold predta_correct_wrt_sign in |- *.
intros.
simpl in H1.
elim (bool_is_true_or_false (N.eqb (iad_conv a a1) a2)); intros; rewrite H2 in H1.
inversion H1.
apply (st_produit_correct_wrt_sign_invar a0 s sigma).
apply (H a a0).
simpl in |- *.
rewrite (Neqb_correct a).
reflexivity.
apply (H0 a1 s).
simpl in |- *.
rewrite (Neqb_correct a1).
reflexivity.
inversion H1.
intros.
elim (predta_correct_wrt_sign_M2 m m0 sigma H1).
intros.
induction a as [| p].
simpl in |- *.
unfold predta_correct_wrt_sign in |- *.
intros.
simpl in H5.
induction a as [| p].
exact (H _ _ _ H3 H2 _ _ H5).
elim (positive_sum p); intros.
rewrite H6 in H5.
exact (H0 _ _ _ H4 H2 _ _ H5).
elim H6; intros; elim H7; intros; rewrite H8 in H5.
elim (positive_sum x); intros.
rewrite H9 in H5.
inversion H5.
elim H9; intros; elim H10; intros; rewrite H11 in H5.
exact (H _ _ _ H3 H2 _ _ H5).
inversion H5.
elim (positive_sum x); intros.
rewrite H9 in H5.
inversion H5.
elim H9; intros; elim H10; intros; rewrite H11 in H5.
exact (H0 _ _ _ H4 H2 _ _ H5).
inversion H5.
induction p as [p Hrecp| p Hrecp| ].
cut (predta_correct_wrt_sign (M1 state (Npos p) s) sigma).
intros.
unfold predta_correct_wrt_sign in |- *.
intros.
simpl in H6.
induction a as [| p0].
inversion H6.
elim (positive_sum p0); intros.
rewrite H7 in H6.
inversion H6.
elim H7; intros; elim H8; intros; rewrite H9 in H6.
elim (positive_sum x); intros.
rewrite H10 in H6.
exact (H _ _ _ H3 H5 _ _ H6).
elim H10; intros; elim H11; intros; rewrite H12 in H6.
inversion H6.
exact (H _ _ _ H3 H5 _ _ H6).
elim (positive_sum x); intros.
rewrite H10 in H6.
exact (H0 _ _ _ H4 H5 _ _ H6).
elim H10; intros; elim H11; intros; rewrite H12 in H6.
inversion H6.
exact (H0 _ _ _ H4 H5 _ _ H6).
unfold predta_correct_wrt_sign in |- *.
simple induction a.
exact (H2 (Npos 1)).
intro.
exact (H2 (Npos (xI p0))).
cut (predta_correct_wrt_sign (M1 state (Npos p) s) sigma).
intro.
unfold predta_correct_wrt_sign in |- *.
intros.
simpl in H6.
induction a as [| p0].
exact (H _ _ _ H3 H5 _ _ H6).
elim (positive_sum p0); intros.
rewrite H7 in H6.
exact (H0 _ _ _ H4 H5 _ _ H6).
elim H7; intros; elim H8; intros; rewrite H9 in H6.
elim (positive_sum x); intros.
rewrite H10 in H6.
inversion H6.
elim H10; intros; elim H11; intros; rewrite H12 in H6.
exact (H _ _ _ H3 H5 _ _ H6).
inversion H6.
elim (positive_sum x); intros.
rewrite H10 in H6.
inversion H6.
elim H10; intros; elim H11; intros; rewrite H12 in H6.
exact (H0 _ _ _ H4 H5 _ _ H6).
inversion H6.
unfold predta_correct_wrt_sign in |- *.
simple induction a.
exact (H2 N0).
intro.
exact (H2 (Npos (xO p0))).
cut (predta_correct_wrt_sign (M1 state N0 s) sigma).
intro.
unfold predta_correct_wrt_sign in |- *.
intros.
simpl in H6.
induction a as [| p].
inversion H6.
elim (positive_sum p); intros.
rewrite H7 in H6.
inversion H6.
elim H7; intros; elim H8; intros; rewrite H9 in H6.
elim (positive_sum x); intros.
rewrite H10 in H6.
exact (H _ _ _ H3 H5 _ _ H6).
elim H10; intros; elim H11; intros; rewrite H12 in H6.
inversion H6.
exact (H _ _ _ H3 H5 _ _ H6).
elim (positive_sum x); intros.
rewrite H10 in H6.
exact (H0 _ _ _ H4 H5 _ _ H6).
elim H10; intros; elim H11; intros; rewrite H12 in H6.
inversion H6.
exact (H0 _ _ _ H4 H5 _ _ H6).
unfold predta_correct_wrt_sign in |- *.
simple induction a.
exact (H2 (Npos 1)).
intro.
exact (H2 (Npos (xI p))).
