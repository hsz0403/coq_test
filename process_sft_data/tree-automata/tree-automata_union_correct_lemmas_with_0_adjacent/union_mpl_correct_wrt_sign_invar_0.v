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

Lemma union_mpl_correct_wrt_sign_invar_0 : forall (s : state) (a : ad) (p : prec_list) (pa : pre_ad) (sigma : signature), state_correct_wrt_sign_with_offset s sigma pa -> state_correct_wrt_sign_with_offset (M1 prec_list a p) sigma pa -> state_correct_wrt_sign_with_offset (union_mpl_0 a p s) sigma pa.
Proof.
simple induction s.
unfold state_correct_wrt_sign_with_offset in |- *.
intros.
exact (H0 _ _ H1).
unfold state_correct_wrt_sign_with_offset in |- *.
intros.
simpl in H1.
elim (bool_is_true_or_false (N.eqb a1 a)); intros; rewrite H2 in H1.
elim (H a a0).
intros.
elim (H0 a p).
intros.
elim H3.
elim H4.
intros.
simpl in H1.
elim (bool_is_true_or_false (N.eqb a1 a2)); intros; rewrite H9 in H1; inversion H1.
rewrite H7 in H5.
inversion H5.
split with x.
rewrite <- H12 in H6.
split.
rewrite <- (Neqb_complete _ _ H9).
rewrite (Neqb_complete _ _ H2).
exact H7.
exact (union_pl_correct_wrt_sign_invar p a0 x H6 H8).
simpl in |- *.
rewrite H2.
reflexivity.
simpl in |- *.
rewrite (Neqb_correct a).
reflexivity.
elim (N.discr (Nxor a a1)).
intro y.
elim y.
intros x y0.
rewrite y0 in H1.
rewrite (MapPut1_semantics prec_list x a a1 a0 p y0) in H1.
elim (bool_is_true_or_false (N.eqb a a2)); intros; rewrite H3 in H1.
inversion H1.
elim (H a a0).
intros.
elim H4.
intros.
split with x0.
rewrite <- (Neqb_complete _ _ H3).
rewrite <- H5.
exact H4.
simpl in |- *.
rewrite (Neqb_correct a).
reflexivity.
elim (bool_is_true_or_false (N.eqb a1 a2)); intros.
rewrite H4 in H1.
inversion H1.
elim (H0 a1 p).
intros.
split with x0.
rewrite (Neqb_complete _ _ H4) in H5.
rewrite H6 in H5.
exact H5.
simpl in |- *.
rewrite (Neqb_correct a1).
reflexivity.
rewrite H4 in H1.
inversion H1.
intros y.
rewrite (Neqb_comm a1 a) in H2.
rewrite (Nxor_eq_true _ _ y) in H2.
inversion H2.
intros.
unfold state_correct_wrt_sign_with_offset in |- *.
intros.
cut (state_correct_wrt_sign_with_offset m sigma (pre_ad_O pa)).
cut (state_correct_wrt_sign_with_offset m0 sigma (pre_ad_I pa)).
intros.
induction a as [| p1].
simpl in H3.
cut (state_correct_wrt_sign_with_offset (M1 prec_list N0 p) sigma (pre_ad_O pa)).
intros.
induction a0 as [| p1].
elim (H _ _ _ _ H5 H6 N0 p0).
intros.
split with x.
simpl in H7.
exact H7.
exact H3.
induction p1 as [p1 Hrecp1| p1 Hrecp1| ].
elim (H4 (Npos p1) p0).
intros.
split with x.
simpl in H7.
exact H7.
exact H3.
elim (H _ _ _ _ H5 H6 (Npos p1) p0).
intros.
split with x.
simpl in H7.
exact H7.
exact H3.
elim (H4 N0 p0).
intros.
split with x.
simpl in H7.
exact H7.
exact H3.
unfold state_correct_wrt_sign_with_offset in |- *.
intros.
elim (H2 (N.double a) p1).
intros.
split with x.
induction a as [| p2]; simpl in |- *; simpl in H7; exact H7.
simpl in H6.
elim (N.discr a).
intros y.
elim y.
intros x y0.
rewrite y0 in H6.
inversion H6.
intros y.
rewrite y in H6.
rewrite y.
simpl in |- *.
exact H6.
induction p1 as [p1 Hrecp1| p1 Hrecp1| ].
cut (state_correct_wrt_sign_with_offset (M1 prec_list (Npos p1) p) sigma (pre_ad_I pa)).
intro.
induction a0 as [| p2].
simpl in H3.
elim (H5 N0 p0).
intros.
split with x.
simpl in H7.
exact H7.
exact H3.
induction p2 as [p2 Hrecp2| p2 Hrecp2| ]; simpl in H3.
elim (H0 _ _ _ _ H4 H6 (Npos p2) p0).
intros.
split with x.
simpl in H7.
exact H7.
exact H3.
elim (H5 (Npos p2) p0).
intros.
split with x.
simpl in H7.
exact H7.
exact H3.
elim (H0 _ _ _ _ H4 H6 N0 p0).
intros.
split with x.
simpl in H7.
exact H7.
exact H3.
unfold state_correct_wrt_sign_with_offset in |- *.
intros.
elim (H2 (Ndouble_plus_one a) p2).
intros.
split with x.
induction a as [| p3]; simpl in |- *; simpl in H7; exact H7.
induction a as [| p3]; simpl in |- *; exact H6.
cut (state_correct_wrt_sign_with_offset (M1 prec_list (Npos p1) p) sigma (pre_ad_O pa)).
intros.
induction a0 as [| p2].
simpl in H3.
elim (H _ _ _ _ H5 H6 N0 p0).
intros.
split with x.
simpl in H7.
exact H7.
exact H3.
induction p2 as [p2 Hrecp2| p2 Hrecp2| ]; simpl in H3.
elim (H4 (Npos p2) p0).
intros.
split with x.
simpl in H7.
exact H7.
exact H3.
elim (H _ _ _ _ H5 H6 (Npos p2) p0).
intros.
split with x.
simpl in H7.
exact H7.
exact H3.
elim (H4 N0 p0).
intros.
split with x.
simpl in H7.
exact H7.
exact H3.
unfold state_correct_wrt_sign_with_offset in |- *.
intros.
elim (H2 (N.double a) p2).
intros.
split with x.
induction a as [| p3]; simpl in |- *; simpl in H7; exact H7.
induction a as [| p3]; simpl in |- *; exact H6.
cut (state_correct_wrt_sign_with_offset (M1 prec_list N0 p) sigma (pre_ad_I pa)).
intro.
induction a0 as [| p1].
simpl in H3.
elim (H5 N0 p0).
intros.
split with x.
simpl in H7.
exact H7.
exact H3.
induction p1 as [p1 Hrecp1| p1 Hrecp1| ]; simpl in H3.
elim (H0 _ _ _ _ H4 H6 (Npos p1) p0).
intros.
split with x.
simpl in H7.
exact H7.
exact H3.
elim (H5 (Npos p1) p0).
intros.
split with x.
simpl in H7.
exact H7.
exact H3.
elim (H0 _ _ _ _ H4 H6 N0 p0).
intros.
split with x.
simpl in H7.
exact H7.
exact H3.
unfold state_correct_wrt_sign_with_offset in |- *.
intros.
elim (H2 (Ndouble_plus_one a) p1).
intros.
split with x.
induction a as [| p2]; simpl in |- *; simpl in H7; exact H7.
induction a as [| p2]; simpl in |- *.
simpl in H6.
exact H6.
simpl in H6.
inversion H6.
unfold state_correct_wrt_sign_with_offset in |- *.
intros.
elim (H1 (Ndouble_plus_one a1) p1).
intros.
split with x.
induction a1 as [| p2]; simpl in H5; simpl in |- *; exact H5.
induction a1 as [| p2]; simpl in |- *; exact H4.
unfold state_correct_wrt_sign_with_offset in |- *.
intros.
elim (H1 (N.double a1) p1).
intros.
split with x.
induction a1 as [| p2]; simpl in |- *; simpl in H5; exact H5.
induction a1 as [| p2]; simpl in |- *; exact H4.
