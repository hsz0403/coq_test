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

Lemma umpl_conv_1_correct_wrt_sign_invar_0 : forall (s : state) (sigma : signature) (pa : pre_ad), state_correct_wrt_sign_with_offset s sigma pa -> state_correct_wrt_sign_with_offset (umpl_conv_1 s) sigma pa.
Proof.
simple induction s.
intros.
simpl in |- *.
exact H.
intros.
simpl in |- *.
unfold state_correct_wrt_sign_with_offset in H.
unfold state_correct_wrt_sign_with_offset in |- *.
intros.
simpl in H0.
elim (H a a0).
intros.
split with x.
elim (bool_is_true_or_false (N.eqb a a1)); intros; rewrite H2 in H0.
inversion H0.
elim H1.
intros.
rewrite (Neqb_complete _ _ H2) in H3.
split.
exact H3.
exact (upl_conv_1_correct_wrt_sign_invar _ _ H5).
inversion H0.
simpl in |- *.
rewrite (Neqb_correct a).
reflexivity.
intros.
unfold state_correct_wrt_sign_with_offset in H1.
unfold state_correct_wrt_sign_with_offset in |- *.
intros.
unfold state_correct_wrt_sign_with_offset in H.
unfold state_correct_wrt_sign_with_offset in H0.
induction a as [| p0].
simpl in H2.
elim (H sigma (pre_ad_O pa)) with (a := N0) (p := p).
intros.
split with x.
simpl in H3.
exact H3.
intros.
elim (H1 (N.double a) p0).
intros.
split with x.
simpl in |- *.
exact H4.
induction a as [| p1]; simpl in |- *; exact H3.
exact H2.
induction p0 as [p0 Hrecp0| p0 Hrecp0| ].
elim (H0 sigma (pre_ad_I pa)) with (a := Npos p0) (p := p).
intros.
split with x.
simpl in H3.
exact H3.
intros.
elim (H1 (Ndouble_plus_one a) p1).
intros.
split with x.
induction a as [| p2].
simpl in H4.
simpl in |- *.
exact H4.
simpl in H4.
simpl in |- *.
exact H4.
induction a as [| p2]; simpl in |- *; exact H3.
simpl in H2.
exact H2.
elim (H sigma (pre_ad_O pa)) with (a := Npos p0) (p := p).
intros.
split with x.
simpl in H3.
exact H3.
intros.
elim (H1 (N.double a) p1).
intros.
split with x.
induction a as [| p2]; simpl in H4; simpl in |- *; exact H4.
induction a as [| p2]; simpl in |- *; exact H3.
simpl in H2.
exact H2.
elim (H0 sigma (pre_ad_I pa)) with (a := N0) (p := p).
intros.
split with x.
simpl in H3.
exact H3.
intros.
elim (H1 (Ndouble_plus_one a) p0).
intros.
split with x.
induction a as [| p1]; simpl in |- *; simpl in H4; exact H4.
induction a as [| p1]; simpl in |- *; exact H3.
simpl in H2.
exact H2.
