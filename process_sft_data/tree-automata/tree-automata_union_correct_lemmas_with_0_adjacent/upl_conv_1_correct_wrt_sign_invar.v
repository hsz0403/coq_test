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

Lemma upl_conv_1_correct_wrt_sign_invar : forall (p : prec_list) (n : nat), pl_tl_length p n -> pl_tl_length (upl_conv_1 p) n.
Proof.
simple induction p; intros.
simpl in |- *.
inversion H1.
simpl in |- *.
exact (pl_tl_S (uad_conv_1 a) (upl_conv_1 p0) n0 (H _ H6)).
exact (pl_tl_propag (uad_conv_1 a) (upl_conv_1 p0) (upl_conv_1 p1) n0 (H _ H6) (H0 _ H7)).
simpl in |- *.
inversion H.
exact pl_tl_O.
