Require Import Bool.
Require Import NArith Ndec Ndigits.
Require Import ZArith.
Require Import Classical_Prop.
From IntMap Require Import Allmaps.
Require Import bases.
Require Import defs.
Require Import semantics.
Require Import signature.
Require Import refcorrect.
Require Import union.

Lemma upl_conv_0_ref_ok_invar : forall (p : prec_list) (a : ad), prec_occur (upl_conv_0 p) a -> exists b : ad, a = uad_conv_0 b /\ prec_occur p b.
Proof.
simple induction p.
intros.
simpl in H1.
inversion H1.
split with a.
split.
reflexivity.
exact (prec_hd a p0 p1).
elim (H a0 H6).
intros.
split with x.
elim H7.
intros.
split.
exact H8.
exact (prec_int0 a x p0 p1 H9).
elim (H0 a0 H6).
intros.
split with x.
elim H7.
intros.
split.
exact H8.
exact (prec_int1 a x p0 p1 H9).
intros.
simpl in H.
inversion H.
