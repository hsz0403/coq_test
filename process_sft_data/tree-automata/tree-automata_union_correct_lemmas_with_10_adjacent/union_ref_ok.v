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

Lemma upl_conv_1_ref_ok_invar : forall (p : prec_list) (a : ad), prec_occur (upl_conv_1 p) a -> exists b : ad, a = uad_conv_1 b /\ prec_occur p b.
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
Admitted.

Lemma udta_conv_0_ref_ok_invar_0 : forall (d : preDTA) (a : ad) (s : state) (c : ad) (p : prec_list) (b : ad), MapGet state (udta_conv_0 d) (uad_conv_0 a) = Some s -> MapGet prec_list s c = Some p -> prec_occur p b -> exists s' : state, (exists p' : prec_list, (exists b' : ad, MapGet state d a = Some s' /\ MapGet prec_list s' c = Some p' /\ p = upl_conv_0 p' /\ s = umpl_conv_0 s' /\ b = uad_conv_0 b' /\ prec_occur p' b')).
Proof.
intros.
elim (u_conv_0_invar_5 d a s H).
intros.
split with x.
elim H2.
intros.
rewrite H3 in H0.
elim (u_conv_0_invar_7 x c p H0).
intros.
split with x0.
elim H5.
intros.
rewrite H6 in H1.
elim (upl_conv_0_ref_ok_invar x0 b H1).
intros.
split with x1.
elim H8.
intros.
split.
exact H4.
split.
exact H7.
split.
exact H6.
split.
exact H3.
split.
exact H9.
Admitted.

Lemma udta_conv_1_ref_ok_invar_0 : forall (d : preDTA) (a : ad) (s : state) (c : ad) (p : prec_list) (b : ad), MapGet state (udta_conv_1 d) (uad_conv_1 a) = Some s -> MapGet prec_list s c = Some p -> prec_occur p b -> exists s' : state, (exists p' : prec_list, (exists b' : ad, MapGet state d a = Some s' /\ MapGet prec_list s' c = Some p' /\ p = upl_conv_1 p' /\ s = umpl_conv_1 s' /\ b = uad_conv_1 b' /\ prec_occur p' b')).
Proof.
intros.
elim (u_conv_1_invar_5 d a s H).
intros.
split with x.
elim H2.
intros.
rewrite H3 in H0.
elim (u_conv_1_invar_7 x c p H0).
intros.
split with x0.
elim H5.
intros.
rewrite H6 in H1.
elim (upl_conv_1_ref_ok_invar x0 b H1).
intros.
split with x1.
elim H8.
intros.
split.
exact H4.
split.
exact H7.
split.
exact H6.
split.
exact H3.
split.
exact H9.
Admitted.

Lemma udta_conv_0_ref_ok_invar : forall d : preDTA, preDTA_ref_ok d -> preDTA_ref_ok (udta_conv_0 d).
Proof.
unfold preDTA_ref_ok in |- *.
intros.
elim (u_conv_0_invar_8 _ _ _ H0).
intros.
rewrite H3 in H0.
elim (udta_conv_0_ref_ok_invar_0 _ _ _ _ _ _ H0 H1 H2).
intros.
elim H4.
intros.
elim H5.
intros.
decompose [and] H6.
elim (H _ _ _ _ _ H7 H9 H13).
intros.
split with (umpl_conv_0 x3).
rewrite H11.
Admitted.

Lemma udta_conv_1_ref_ok_invar : forall d : preDTA, preDTA_ref_ok d -> preDTA_ref_ok (udta_conv_1 d).
Proof.
unfold preDTA_ref_ok in |- *.
intros.
elim (u_conv_1_invar_8 _ _ _ H0).
intros.
rewrite H3 in H0.
elim (udta_conv_1_ref_ok_invar_0 _ _ _ _ _ _ H0 H1 H2).
intros.
elim H4.
intros.
elim H5.
intros.
decompose [and] H6.
elim (H _ _ _ _ _ H7 H9 H13).
intros.
split with (umpl_conv_1 x3).
rewrite H11.
Admitted.

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
Admitted.

Lemma u_merge_ref_ok_invar : forall d0 d1 : preDTA, preDTA_ref_ok d0 -> preDTA_ref_ok d1 -> preDTA_ref_ok (u_merge d0 d1).
Proof.
unfold u_merge in |- *.
Admitted.

Lemma union_pl_ref_ok_invar : forall (p p' : prec_list) (d : preDTA), prec_list_ref_ok p d -> prec_list_ref_ok p' d -> prec_list_ref_ok (union_pl p p') d.
Proof.
simple induction p.
simpl in |- *.
intros.
unfold prec_list_ref_ok in |- *.
elim (prec_list_ref_ok_destr a p0 p1 d H1).
intros.
inversion H5.
rewrite <- H6.
exact (H1 a (prec_hd a p0 p1)).
exact (H3 a0 H10).
exact (H0 p' d H4 H2 a0 H10).
intros.
unfold prec_list_ref_ok in |- *.
intros.
simpl in H1.
Admitted.

Lemma union_mpl_0_ref_ok_invar : forall (s : state) (a : ad) (p : prec_list) (d : preDTA), state_ref_ok (M1 prec_list a p) d -> state_ref_ok s d -> state_ref_ok (union_mpl_0 a p s) d.
Proof.
simple induction s.
simpl in |- *.
intros.
exact H.
intros.
simpl in |- *.
unfold state_ref_ok in |- *.
intros.
elim (bool_is_true_or_false (N.eqb a1 a)); intros; rewrite H2 in H1.
simpl in H1.
elim (bool_is_true_or_false (N.eqb a1 a2)); intros; rewrite H3 in H1.
inversion H1.
apply (union_pl_ref_ok_invar p a0 d).
apply (H a1).
simpl in |- *.
rewrite (Neqb_correct a1).
reflexivity.
apply (H0 a).
simpl in |- *.
rewrite (Neqb_correct a).
reflexivity.
inversion H1.
elim (N.discr (Nxor a a1)); intros y.
elim y.
intros x y0.
rewrite y0 in H1.
rewrite (MapPut1_semantics prec_list x a a1 a0 p) in H1.
elim (bool_is_true_or_false (N.eqb a a2)); intros; rewrite H3 in H1.
inversion H1.
rewrite <- H5.
apply (H0 a).
simpl in |- *.
rewrite (Neqb_correct a).
reflexivity.
elim (bool_is_true_or_false (N.eqb a1 a2)); intros; rewrite H4 in H1; inversion H1.
rewrite <- H6.
apply (H a1).
simpl in |- *.
rewrite (Neqb_correct a1).
reflexivity.
exact y0.
rewrite (Neqb_comm a1 a) in H2.
rewrite (Nxor_eq_true _ _ y) in H2.
inversion H2.
intros.
simpl in |- *.
unfold state_ref_ok in |- *.
intros.
cut (state_ref_ok m0 d).
cut (state_ref_ok m d).
intros.
induction a as [| p1].
induction a0 as [| p1].
simpl in H3.
exact (H _ _ _ H1 H4 N0 p0 H3).
induction p1 as [p1 Hrecp1| p1 Hrecp1| ]; simpl in H3.
exact (H5 _ _ H3).
exact (H _ _ _ H1 H4 _ _ H3).
exact (H5 _ _ H3).
induction p1 as [p1 Hrecp1| p1 Hrecp1| ].
clear Hrecp1.
induction a0 as [| p2].
simpl in H3.
exact (H4 _ _ H3).
cut (state_ref_ok (M1 prec_list (Npos p1) p) d).
intro.
induction p2 as [p2 Hrecp2| p2 Hrecp2| ]; simpl in H3.
exact (H0 _ _ _ H6 H5 _ _ H3).
exact (H4 _ _ H3).
exact (H0 _ _ _ H6 H5 _ _ H3).
unfold state_ref_ok in |- *.
intros.
apply (H1 (Ndouble_plus_one a) p3).
induction a as [| p4]; simpl in |- *; exact H6.
cut (state_ref_ok (M1 prec_list (Npos p1) p) d).
intro.
induction a0 as [| p2].
simpl in H3.
exact (H _ _ _ H6 H4 _ _ H3).
induction p2 as [p2 Hrecp2| p2 Hrecp2| ]; simpl in H3.
exact (H5 _ _ H3).
exact (H _ _ _ H6 H4 _ _ H3).
exact (H5 _ _ H3).
unfold state_ref_ok in |- *.
intros.
apply (H1 (N.double a) p2).
induction a as [| p3]; simpl in |- *; exact H6.
cut (state_ref_ok (M1 prec_list N0 p) d).
intros.
induction a0 as [| p1].
simpl in H3.
exact (H4 _ _ H3).
induction p1 as [p1 Hrecp1| p1 Hrecp1| ]; simpl in H3.
exact (H0 _ _ _ H6 H5 _ _ H3).
exact (H4 _ _ H3).
exact (H0 _ _ _ H6 H5 _ _ H3).
unfold state_ref_ok in |- *.
intros.
apply (H1 (Ndouble_plus_one a) p1).
induction a as [| p2]; exact H6.
unfold state_ref_ok in |- *.
intros.
apply (H2 (N.double a1) p1).
induction a1 as [| p2]; exact H4.
unfold state_ref_ok in |- *.
intros.
apply (H2 (Ndouble_plus_one a1) p1).
Admitted.

Lemma union_mpl_correct_ref_ok_invar : forall (s0 s1 : state) (d : preDTA), state_ref_ok s0 d -> state_ref_ok s1 d -> state_ref_ok (union_mpl s0 s1) d.
Proof.
simple induction s0.
simpl in |- *.
intros.
induction s1 as [| a a0| s1_1 Hrecs1_1 s1_0 Hrecs1_0].
exact H.
exact H0.
exact H0.
simple induction s1.
simpl in |- *.
intros.
exact H.
intros.
replace (union_mpl (M1 prec_list a a0) (M1 prec_list a1 a2)) with (union_mpl_0 a1 a2 (M1 prec_list a a0)).
exact (union_mpl_0_ref_ok_invar _ _ _ _ H0 H).
reflexivity.
intros.
replace (union_mpl (M1 prec_list a a0) (M2 prec_list m m0)) with (union_mpl_0 a a0 (M2 prec_list m m0)).
exact (union_mpl_0_ref_ok_invar _ _ _ _ H1 H2).
reflexivity.
simple induction s1.
intros.
simpl in |- *.
exact H1.
intros.
replace (union_mpl (M2 prec_list m m0) (M1 prec_list a a0)) with (union_mpl_0 a a0 (M2 prec_list m m0)).
exact (union_mpl_0_ref_ok_invar _ _ _ _ H2 H1).
reflexivity.
intros.
elim (state_ref_ok_M2_destr _ _ _ H3).
intros.
elim (state_ref_ok_M2_destr _ _ _ H4).
intros.
simpl in |- *.
unfold state_ref_ok in |- *.
intros.
induction a as [| p0].
simpl in H9.
exact (H _ _ H5 H7 _ _ H9).
induction p0 as [p0 Hrecp0| p0 Hrecp0| ]; simpl in H9.
exact (H0 _ _ H6 H8 _ _ H9).
exact (H _ _ H5 H7 _ _ H9).
Admitted.

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
Admitted.

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
