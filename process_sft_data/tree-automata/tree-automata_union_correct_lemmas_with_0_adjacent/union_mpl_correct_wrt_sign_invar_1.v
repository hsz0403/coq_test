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

Lemma union_mpl_correct_wrt_sign_invar_1 : forall (s0 s1 : state) (pa : pre_ad) (sigma : signature), state_correct_wrt_sign_with_offset s0 sigma pa -> state_correct_wrt_sign_with_offset s1 sigma pa -> state_correct_wrt_sign_with_offset (union_mpl s0 s1) sigma pa.
Proof.
simple induction s0.
simpl in |- *.
simple induction s1; intros.
exact H0.
exact H0.
exact H2.
simpl in |- *.
simple induction s1.
intros.
exact (union_mpl_correct_wrt_sign_invar_0 (M0 prec_list) a a0 pa sigma H0 H).
intros.
elim (bool_is_true_or_false (N.eqb a1 a)); intros; rewrite H1.
unfold state_correct_wrt_sign_with_offset in |- *.
intros.
simpl in H2.
elim (bool_is_true_or_false (N.eqb a1 a3)); intros; rewrite H3 in H2.
inversion H2.
elim (H a a0).
intros.
elim (H0 a1 a2).
intros.
split with x.
rewrite (Neqb_complete _ _ H1) in H6.
split.
elim H4.
intros.
rewrite <- (Neqb_complete _ _ H3).
rewrite (Neqb_complete _ _ H1).
exact H7.
elim H4.
elim H6.
intros.
rewrite H9 in H7.
inversion H7.
rewrite H12 in H10.
exact (union_pl_correct_wrt_sign_invar _ _ _ H8 H10).
simpl in |- *.
rewrite (Neqb_correct a1).
reflexivity.
simpl in |- *.
rewrite (Neqb_correct a).
reflexivity.
inversion H2.
elim (N.discr (Nxor a a1)); intro y.
elim y.
intros x y0.
rewrite y0.
unfold state_correct_wrt_sign_with_offset in |- *.
intros.
rewrite (MapPut1_semantics prec_list x a a1 a0 a2) in H2.
elim (bool_is_true_or_false (N.eqb a a3)); intros.
rewrite H3 in H2.
inversion H2.
elim (H a a0).
intros.
split with x0.
rewrite (Neqb_complete _ _ H3) in H4.
rewrite H5 in H4.
exact H4.
simpl in |- *.
rewrite (Neqb_correct a).
reflexivity.
rewrite H3 in H2.
elim (bool_is_true_or_false (N.eqb a1 a3)); intros.
rewrite H4 in H2.
inversion H2.
elim (H0 a1 a2).
intros.
split with x0.
rewrite (Neqb_complete _ _ H4) in H5.
rewrite H6 in H5.
exact H5.
simpl in |- *.
rewrite (Neqb_correct a1).
reflexivity.
rewrite H4 in H2.
inversion H2.
exact y0.
rewrite (Neqb_comm a1 a) in H1.
rewrite (Nxor_eq_true _ _ y) in H1.
inversion H1.
intros.
simpl in |- *.
induction a as [| p].
exact (union_mpl_correct_wrt_sign_invar_0 _ _ _ _ _ H2 H1).
induction p as [p Hrecp| p Hrecp| ].
clear Hrecp.
replace (state_correct_wrt_sign_with_offset (M2 prec_list m (union_mpl_0 (Npos p) a0 m0)) sigma pa) with (state_correct_wrt_sign_with_offset (union_mpl_0 (Npos (xI p)) a0 (M2 prec_list m m0)) sigma pa).
exact (union_mpl_correct_wrt_sign_invar_0 (M2 prec_list m m0) (Npos (xI p)) a0 pa sigma H2 H1).
reflexivity.
clear Hrecp.
replace (state_correct_wrt_sign_with_offset (M2 prec_list (union_mpl_0 (Npos p) a0 m) m0) sigma pa) with (state_correct_wrt_sign_with_offset (union_mpl_0 (Npos (xO p)) a0 (M2 prec_list m m0)) sigma pa).
exact (union_mpl_correct_wrt_sign_invar_0 (M2 prec_list m m0) (Npos (xO p)) a0 pa sigma H2 H1).
reflexivity.
replace (state_correct_wrt_sign_with_offset (M2 prec_list m (union_mpl_0 N0 a0 m0)) sigma pa) with (state_correct_wrt_sign_with_offset (union_mpl_0 (Npos 1) a0 (M2 prec_list m m0)) sigma pa).
exact (union_mpl_correct_wrt_sign_invar_0 (M2 prec_list m m0) (Npos 1) a0 pa sigma H2 H1).
reflexivity.
simple induction s1.
intros.
simpl in |- *.
exact H1.
intros.
simpl in |- *.
induction a as [| p].
replace (state_correct_wrt_sign_with_offset (M2 prec_list (union_mpl_0 N0 a0 m) m0) sigma pa) with (state_correct_wrt_sign_with_offset (union_mpl_0 N0 a0 (M2 prec_list m m0)) sigma pa).
exact (union_mpl_correct_wrt_sign_invar_0 (M2 prec_list m m0) N0 a0 pa sigma H1 H2).
reflexivity.
induction p as [p Hrecp| p Hrecp| ].
replace (state_correct_wrt_sign_with_offset (M2 prec_list m (union_mpl_0 (Npos p) a0 m0)) sigma pa) with (state_correct_wrt_sign_with_offset (union_mpl_0 (Npos (xI p)) a0 (M2 prec_list m m0)) sigma pa).
exact (union_mpl_correct_wrt_sign_invar_0 (M2 prec_list m m0) (Npos (xI p)) a0 pa sigma H1 H2).
reflexivity.
replace (state_correct_wrt_sign_with_offset (M2 prec_list (union_mpl_0 (Npos p) a0 m) m0) sigma pa) with (state_correct_wrt_sign_with_offset (union_mpl_0 (Npos (xO p)) a0 (M2 prec_list m m0)) sigma pa).
exact (union_mpl_correct_wrt_sign_invar_0 (M2 prec_list m m0) (Npos (xO p)) a0 pa sigma H1 H2).
reflexivity.
replace (state_correct_wrt_sign_with_offset (M2 prec_list m (union_mpl_0 N0 a0 m0)) sigma pa) with (state_correct_wrt_sign_with_offset (union_mpl_0 (Npos 1) a0 (M2 prec_list m m0)) sigma pa).
exact (union_mpl_correct_wrt_sign_invar_0 (M2 prec_list m m0) (Npos 1) a0 pa sigma H1 H2).
reflexivity.
intros.
simpl in |- *.
elim (state_correct_wrt_sign_with_offset_M2 _ _ _ _ H3).
elim (state_correct_wrt_sign_with_offset_M2 _ _ _ _ H4).
intros.
cut (state_correct_wrt_sign_with_offset (union_mpl m m1) sigma (pre_ad_O pa)).
cut (state_correct_wrt_sign_with_offset (union_mpl m0 m2) sigma (pre_ad_I pa)).
intros.
unfold state_correct_wrt_sign_with_offset in |- *.
intros.
induction a as [| p0].
elim (H10 N0 p).
intros.
split with x.
simpl in H12.
exact H12.
simpl in H11.
exact H11.
induction p0 as [p0 Hrecp0| p0 Hrecp0| ].
elim (H9 (Npos p0) p).
intros.
split with x.
simpl in H12.
exact H12.
simpl in H11.
exact H11.
elim (H10 (Npos p0) p).
intros.
split with x.
simpl in H12.
exact H12.
simpl in H11.
exact H11.
elim (H9 N0 p).
intros.
simpl in H12.
simpl in H11.
split with x.
exact H12.
exact H11.
exact (H0 _ _ _ H8 H6).
exact (H _ _ _ H7 H5).
