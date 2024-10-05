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

Lemma inter_DTA_main_state_correct_invar : forall d0 d1 : DTA, DTA_main_state_correct d0 -> DTA_main_state_correct d1 -> DTA_main_state_correct (inter d0 d1).
Proof.
simple induction d0.
simple induction d1.
simpl in |- *.
unfold addr_in_preDTA in |- *.
intros.
elim H.
intros.
elim H0.
intros.
split with (s_produit x x0).
exact (predta_produit_2 _ _ _ _ _ _ H1 H2).
