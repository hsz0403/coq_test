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

Lemma upl_conv_0_correct_wrt_sign_invar : forall (p : prec_list) (n : nat), pl_tl_length p n -> pl_tl_length (upl_conv_0 p) n.
Proof.
simple induction p; intros.
simpl in |- *.
inversion H1.
simpl in |- *.
exact (pl_tl_S (uad_conv_0 a) (upl_conv_0 p0) n0 (H _ H6)).
exact (pl_tl_propag (uad_conv_0 a) (upl_conv_0 p0) (upl_conv_0 p1) n0 (H _ H6) (H0 _ H7)).
simpl in |- *.
inversion H.
Admitted.

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
Admitted.

Lemma umpl_conv_0_correct_wrt_sign_invar : forall (s : state) (sigma : signature), state_correct_wrt_sign s sigma -> state_correct_wrt_sign (umpl_conv_0 s) sigma.
Proof.
unfold state_correct_wrt_sign in |- *.
intros.
elim (umpl_conv_0_correct_wrt_sign_invar_0 s sigma pre_ad_empty) with (a := a) (p := p).
intros.
split with x.
simpl in H1.
exact H1.
unfold state_correct_wrt_sign_with_offset in |- *.
simpl in |- *.
exact H.
Admitted.

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
Admitted.

Lemma umpl_conv_1_correct_wrt_sign_invar : forall (s : state) (sigma : signature), state_correct_wrt_sign s sigma -> state_correct_wrt_sign (umpl_conv_1 s) sigma.
Proof.
unfold state_correct_wrt_sign in |- *.
intros.
elim (umpl_conv_1_correct_wrt_sign_invar_0 s sigma pre_ad_empty) with (a := a) (p := p).
intros.
split with x.
simpl in H1.
exact H1.
unfold state_correct_wrt_sign_with_offset in |- *.
simpl in |- *.
exact H.
Admitted.

Lemma udta_conv_0_correct_wrt_sign_invar_0 : forall (d : preDTA) (sigma : signature), predta_correct_wrt_sign d sigma -> predta_correct_wrt_sign (udta_conv_0_aux d) sigma.
Proof.
unfold predta_correct_wrt_sign in |- *.
simple induction d.
intros.
inversion H0.
intros.
simpl in H0.
elim (bool_is_true_or_false (N.eqb a a1)); intros.
rewrite H1 in H0.
inversion H0.
apply (umpl_conv_0_correct_wrt_sign_invar a0 sigma).
apply (H a a0).
simpl in |- *.
rewrite (Neqb_correct a).
reflexivity.
rewrite H1 in H0.
inversion H0.
intros.
simpl in H2.
induction a as [| p].
apply (H sigma) with (a := N0) (s := s).
intros.
apply (H1 (N.double a) s0).
induction a as [| p]; simpl in |- *; exact H3.
exact H2.
induction p as [p Hrecp| p Hrecp| ]; simpl in H2.
apply (H0 sigma) with (a := Npos p) (s := s).
intros.
apply (H1 (Ndouble_plus_one a) s0).
induction a as [| p0]; simpl in |- *; exact H3.
exact H2.
apply (H sigma) with (a := Npos p) (s := s).
intros.
apply (H1 (N.double a) s0).
induction a as [| p0]; simpl in |- *; exact H3.
exact H2.
apply (H0 sigma) with (a := N0) (s := s).
intros.
apply (H1 (Ndouble_plus_one a) s0).
induction a as [| p]; simpl in |- *; exact H3.
Admitted.

Lemma udta_conv_0_correct_wrt_sign_invar : forall (d : preDTA) (sigma : signature), predta_correct_wrt_sign d sigma -> predta_correct_wrt_sign (udta_conv_0 d) sigma.
Proof.
unfold udta_conv_0 in |- *.
intros.
unfold predta_correct_wrt_sign in |- *.
intros.
induction a as [| p].
simpl in H0.
exact (udta_conv_0_correct_wrt_sign_invar_0 d sigma H N0 s H0).
induction p as [p Hrecp| p Hrecp| ]; simpl in H0.
inversion H0.
exact (udta_conv_0_correct_wrt_sign_invar_0 d sigma H (Npos p) s H0).
Admitted.

Lemma udta_conv_1_correct_wrt_sign_invar_0 : forall (d : preDTA) (sigma : signature), predta_correct_wrt_sign d sigma -> predta_correct_wrt_sign (udta_conv_1_aux d) sigma.
Proof.
unfold predta_correct_wrt_sign in |- *.
simple induction d.
intros.
inversion H0.
intros.
simpl in H0.
elim (bool_is_true_or_false (N.eqb a a1)); intros.
rewrite H1 in H0.
inversion H0.
apply (umpl_conv_1_correct_wrt_sign_invar a0 sigma).
apply (H a a0).
simpl in |- *.
rewrite (Neqb_correct a).
reflexivity.
rewrite H1 in H0.
inversion H0.
intros.
simpl in H2.
induction a as [| p].
apply (H sigma) with (a := N0) (s := s).
intros.
apply (H1 (N.double a) s0).
induction a as [| p]; simpl in |- *; exact H3.
exact H2.
induction p as [p Hrecp| p Hrecp| ]; simpl in H2.
apply (H0 sigma) with (a := Npos p) (s := s).
intros.
apply (H1 (Ndouble_plus_one a) s0).
induction a as [| p0]; simpl in |- *; exact H3.
exact H2.
apply (H sigma) with (a := Npos p) (s := s).
intros.
apply (H1 (N.double a) s0).
induction a as [| p0]; simpl in |- *; exact H3.
exact H2.
apply (H0 sigma) with (a := N0) (s := s).
intros.
apply (H1 (Ndouble_plus_one a) s0).
induction a as [| p]; simpl in |- *; exact H3.
Admitted.

Lemma udta_conv_1_correct_wrt_sign_invar : forall (d : preDTA) (sigma : signature), predta_correct_wrt_sign d sigma -> predta_correct_wrt_sign (udta_conv_1 d) sigma.
Proof.
unfold udta_conv_1 in |- *.
intros.
unfold predta_correct_wrt_sign in |- *.
intros.
induction a as [| p].
simpl in H0.
inversion H0.
induction p as [p Hrecp| p Hrecp| ]; simpl in H0.
exact (udta_conv_1_correct_wrt_sign_invar_0 d sigma H (Npos p) s H0).
inversion H0.
Admitted.

Lemma umerge_correct_wrt_sign_invar : forall (d0 d1 : preDTA) (sigma : signature), predta_correct_wrt_sign d0 sigma -> predta_correct_wrt_sign d1 sigma -> predta_correct_wrt_sign (u_merge d0 d1) sigma.
Proof.
unfold predta_correct_wrt_sign in |- *.
intros.
elim (adcnv_disj a).
intros.
elim H2; intros.
elim (u_conv_0_invar_5 d0 x s).
intros.
elim H4.
intros.
apply (udta_conv_0_correct_wrt_sign_invar d0 sigma H a s).
exact (u_merge_0r d0 d1 a s H1 x H3).
rewrite <- H3.
exact (u_merge_0r d0 d1 a s H1 x H3).
elim (u_conv_1_invar_5 d1 x s).
intros.
elim H4.
intros.
apply (udta_conv_1_correct_wrt_sign_invar d1 sigma H0 a s).
exact (u_merge_1r d0 d1 a s H1 x H3).
rewrite <- H3.
Admitted.

Lemma union_pl_correct_wrt_sign_invar : forall (p0 p1 : prec_list) (n : nat), pl_tl_length p0 n -> pl_tl_length p1 n -> pl_tl_length (union_pl p0 p1) n.
Proof.
simple induction p0.
intros.
simpl in |- *.
inversion H1.
simpl in |- *.
rewrite <- H4 in H2.
exact (pl_tl_propag a p p2 n0 H7 H2).
rewrite <- H5 in H2.
exact (pl_tl_propag a p (union_pl p1 p2) n0 H7 (H0 p2 (S n0) H8 H2)).
intros.
inversion H.
rewrite <- H2 in H0.
inversion H0.
simpl in |- *.
Admitted.

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
Admitted.

Lemma umpl_conv_0_correct_wrt_sign_invar_0 : forall (s : state) (sigma : signature) (pa : pre_ad), state_correct_wrt_sign_with_offset s sigma pa -> state_correct_wrt_sign_with_offset (umpl_conv_0 s) sigma pa.
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
exact (upl_conv_0_correct_wrt_sign_invar _ _ H5).
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
