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

Lemma MapMerge_ref_ok_invar : forall d0 d1 : preDTA, preDTA_ref_ok d0 -> preDTA_ref_ok d1 -> preDTA_ref_ok (MapMerge state d0 d1).
Proof.
unfold preDTA_ref_ok in |- *.
intros.
rewrite (MapMerge_semantics state d0 d1) in H1.
rewrite (MapMerge_semantics state d0 d1).
elim (option_sum state (MapGet state d1 a)); intros y.
elim y.
intros x y0.
rewrite y0 in H1.
inversion H1.
rewrite <- H5 in H2.
elim (H0 a x c pl b y0 H2 H3).
intros.
rewrite H4.
split with x0.
reflexivity.
rewrite y in H1.
elim (H a s c pl b H1 H2 H3).
intros.
rewrite H4.
elim (option_sum state (MapGet state d1 b)).
intros y0.
elim y0.
intros x0 y1.
rewrite y1.
split with x0.
reflexivity.
intro y0.
rewrite y0.
split with x.
reflexivity.
