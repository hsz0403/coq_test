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

Lemma pl_produit_ref_ok_lem_4 : forall (a : ad) (la ls p : prec_list), pl_produit_ref_ok_0 la p -> pl_produit_ref_ok_1 ls p -> pl_produit_ref_ok_1 (prec_cons a la ls) p.
Proof.
unfold pl_produit_ref_ok_0, pl_produit_ref_ok_1 in |- *.
intros.
elim (nat_sum n); intros.
rewrite H2 in H1.
inversion H1.
elim H2.
intros.
rewrite H3 in H1.
elim (pl_sum p).
intros.
rewrite H4 in H1.
inversion H1.
intros.
elim H4.
intros.
elim H5.
intros.
elim H6.
intros.
rewrite H7 in H1.
cut (pl_produit_1 (prec_cons a la ls) (S x) (prec_cons x0 x1 x2) = pl_produit_0 a la (prec_cons x0 x1 x2) x (pl_produit_1 ls x (prec_cons x0 x1 x2))).
intro.
rewrite H8 in H1.
rewrite <- H7 in H1.
elim (H _ _ _ _ H1).
intros.
elim H9.
intros.
elim H10.
intros.
elim H11.
intros.
elim H13.
intros.
split with x3.
split with x4.
split.
exact H12.
split.
exact (prec_int0 a x3 la ls H14).
exact H15.
intros.
elim H9.
intros.
elim H10.
intros.
elim H11.
intros.
split with a.
split with x3.
split.
exact H12.
split.
exact (prec_hd a la ls).
exact H13.
intros.
elim (H0 _ _ H10).
intros.
elim H11.
intros.
elim H12.
intros.
elim H14.
intros.
split with x3.
split with x4.
split.
exact H13.
split.
exact (prec_int1 a _ la _ H15).
exact H16.
reflexivity.
