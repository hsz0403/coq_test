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

Lemma union_ref_ok : forall d0 d1 : DTA, DTA_ref_ok d0 -> DTA_ref_ok d1 -> DTA_ref_ok (union d0 d1).
Proof.
simple induction d0.
simple induction d1.
unfold union in |- *.
unfold DTA_ref_ok in |- *.
unfold union_1 in |- *.
unfold insert_main_ostate in |- *.
unfold insert_main_ostate_0 in |- *.
unfold insert_ostate in |- *.
intros.
unfold preDTA_ref_ok in |- *.
unfold union_0 in |- *.
unfold union_opt_state in |- *.
elim (option_sum state (MapGet state (u_merge p p0) (uad_conv_0 a))).
intro y.
elim y.
intro x.
intro y0.
rewrite y0.
elim (option_sum state (MapGet state (u_merge p p0) (uad_conv_1 a0))); intro y1.
elim y1.
intro x0.
intro y2.
rewrite y2.
intros.
rewrite (MapPut_semantics state (u_merge p p0) (new_preDTA_ad (u_merge p p0)) (union_mpl x x0)).
rewrite (MapPut_semantics state (u_merge p p0) (new_preDTA_ad (u_merge p p0)) (union_mpl x x0)) in H1.
elim (bool_is_true_or_false (N.eqb (new_preDTA_ad (u_merge p p0)) a1)); intros; rewrite H4 in H1.
inversion H1.
elim (bool_is_true_or_false (N.eqb (new_preDTA_ad (u_merge p p0)) b)); intros; rewrite H5.
split with (union_mpl x x0).
reflexivity.
cut (state_ref_ok (union_mpl x x0) (u_merge p p0)).
intro.
rewrite <- H6 in H2.
exact (H7 c pl H2 b H3).
apply (union_mpl_correct_ref_ok_invar x x0 (u_merge p p0)).
elim (preDTA_ref_ok_def (u_merge p p0)).
intros.
exact (H7 (u_merge_ref_ok_invar p p0 H H0) _ _ y0).
elim (preDTA_ref_ok_def (u_merge p p0)).
intros.
exact (H7 (u_merge_ref_ok_invar p p0 H H0) _ _ y2).
elim (u_merge_ref_ok_invar p p0 H H0 a1 s c pl b H1 H2 H3).
intros.
elim (bool_is_true_or_false (N.eqb (new_preDTA_ad (u_merge p p0)) b)); intros; rewrite H6.
split with (union_mpl x x0).
reflexivity.
split with x1.
exact H5.
rewrite y1.
intros.
rewrite (MapPut_semantics state (u_merge p p0) (new_preDTA_ad (u_merge p p0)) x) .
rewrite (MapPut_semantics state (u_merge p p0) (new_preDTA_ad (u_merge p p0)) x) in H1.
elim (bool_is_true_or_false (N.eqb (new_preDTA_ad (u_merge p p0)) a1)); intros; rewrite H4 in H1.
inversion H1.
rewrite <- H6.
elim (bool_is_true_or_false (N.eqb (new_preDTA_ad (u_merge p p0)) b)); intros; rewrite H5.
split with x.
reflexivity.
elim (preDTA_ref_ok_def (u_merge p p0)).
intros.
rewrite <- H6 in H2.
exact (H7 (u_merge_ref_ok_invar _ _ H H0) (uad_conv_0 a) x y0 c pl H2 b H3).
elim (bool_is_true_or_false (N.eqb (new_preDTA_ad (u_merge p p0)) b)); intros; rewrite H5.
split with x.
reflexivity.
exact (u_merge_ref_ok_invar _ _ H H0 a1 s c pl b H1 H2 H3).
intro y.
rewrite y.
elim (option_sum state (MapGet state (u_merge p p0) (uad_conv_1 a0))); intros.
elim a1.
intros x y1.
rewrite y1.
rewrite y1 in H1.
rewrite (MapPut_semantics state (u_merge p p0) (new_preDTA_ad (u_merge p p0)) x) .
rewrite (MapPut_semantics state (u_merge p p0) (new_preDTA_ad (u_merge p p0)) x) in H1.
elim (bool_is_true_or_false (N.eqb (new_preDTA_ad (u_merge p p0)) b)); intros; rewrite H4.
split with x.
reflexivity.
elim (bool_is_true_or_false (N.eqb (new_preDTA_ad (u_merge p p0)) a2)); intros; rewrite H5 in H1.
inversion H1.
rewrite <- H7 in H2.
exact (u_merge_ref_ok_invar _ _ H H0 _ _ c pl b y1 H2 H3).
exact (u_merge_ref_ok _ _ H H0 _ _ _ _ _ H1 H2 H3).
rewrite b.
rewrite b in H1.
exact (u_merge_ref_ok _ _ H H0 _ _ _ _ _ H1 H2 H3).
