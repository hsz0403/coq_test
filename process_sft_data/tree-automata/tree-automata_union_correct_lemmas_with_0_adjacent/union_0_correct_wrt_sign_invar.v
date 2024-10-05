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

Lemma union_0_correct_wrt_sign_invar : forall (d : preDTA) (a0 a1 : ad) (s : state) (sigma : signature), predta_correct_wrt_sign d sigma -> union_0 d a0 a1 = Some s -> state_correct_wrt_sign s sigma.
Proof.
unfold union_0 in |- *.
unfold union_opt_state in |- *.
intros.
elim (option_sum state (MapGet state d (uad_conv_0 a0))); intros y.
elim y.
intros x y0.
rewrite y0 in H0.
elim (option_sum state (MapGet state d (uad_conv_1 a1))); intros y1.
elim y1.
intros x0 y2.
rewrite y2 in H0.
inversion H0.
apply (union_mpl_correct_wrt_sign_invar x x0 sigma).
unfold predta_correct_wrt_sign in H.
exact (H _ _ y0).
unfold predta_correct_wrt_sign in H.
exact (H _ _ y2).
rewrite y1 in H0.
inversion H0.
rewrite <- H2.
exact (H _ _ y0).
rewrite y in H0.
elim (option_sum state (MapGet state d (uad_conv_1 a1))).
intros y0.
elim y0.
intros x y1.
rewrite y1 in H0.
inversion H0.
rewrite <- H2.
exact (H _ _ y1).
intros y0.
rewrite y0 in H0.
inversion H0.
