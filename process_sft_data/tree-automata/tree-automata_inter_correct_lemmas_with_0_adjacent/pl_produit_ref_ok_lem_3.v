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

Lemma pl_produit_ref_ok_lem_3 : forall (a : ad) (la ls p : prec_list), pl_produit_ref_ok_0 p ls -> pl_produit_ref_ok_1 p la -> pl_produit_ref_ok_0 p (prec_cons a la ls).
Proof.
unfold pl_produit_ref_ok_0, pl_produit_ref_ok_1 in |- *.
intros.
elim (nat_sum n); intros.
rewrite H2 in H1.
inversion H1.
elim H2.
intros.
rewrite H3 in H1.
cut (pl_produit_0 a0 p (prec_cons a la ls) (S x) l = prec_cons (iad_conv a0 a) (pl_produit_1 p x la) (pl_produit_0 a0 p ls x l)).
intros.
rewrite H4 in H1.
inversion H1.
right.
left.
split with a.
split.
reflexivity.
exact (prec_hd a la ls).
left.
elim (H0 b x H9).
intros.
elim H10.
intros.
elim H11.
intros.
elim H12.
intros.
elim H13.
intros.
split with x0.
split with x1.
split.
exact H12.
split.
exact H14.
exact (prec_int0 a x1 la ls H15).
elim (H _ _ _ _ H9).
intros.
left.
elim H10.
intros.
elim H11.
intros.
elim H12.
intros.
elim H14.
intros.
split with x0.
split with x1.
split.
exact H13.
split.
exact H15.
exact (prec_int1 a _ la _ H16).
intros.
elim H10.
intros.
right.
left.
elim H11.
intros.
elim H12.
intros.
split with x0.
split.
exact H13.
exact (prec_int1 a _ la _ H14).
intros.
right.
right.
exact H11.
reflexivity.
