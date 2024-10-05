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

Lemma union_DTA_main_state_correct_invar : forall d0 d1 : DTA, DTA_main_state_correct d0 -> DTA_main_state_correct d1 -> DTA_main_state_correct (union d0 d1).
Proof.
simple induction d0.
simple induction d1.
simpl in |- *.
unfold addr_in_preDTA in |- *.
intros.
elim H.
elim H0.
intros.
unfold union_0 in |- *.
rewrite (u_merge_0 p p0 (uad_conv_0 a) (umpl_conv_0 x0) (u_conv_0_invar_0 p a x0 H2)).
rewrite (u_merge_1 p p0 (uad_conv_1 a0) (umpl_conv_1 x) (u_conv_1_invar_0 p0 a0 x H1)).
unfold insert_ostate in |- *.
unfold union_opt_state in |- *.
split with (union_mpl (umpl_conv_0 x0) (umpl_conv_1 x)).
rewrite (MapPut_semantics state (u_merge p p0) (N.min (N.double (new_preDTA_ad (MapMerge state (udta_conv_0_aux p) (M0 state)))) (Ndouble_plus_one (new_preDTA_ad (udta_conv_1_aux p0)))) (union_mpl (umpl_conv_0 x0) (umpl_conv_1 x))).
rewrite (Neqb_correct (N.min (N.double (new_preDTA_ad (MapMerge state (udta_conv_0_aux p) (M0 state)))) (Ndouble_plus_one (new_preDTA_ad (udta_conv_1_aux p0))))) .
reflexivity.
