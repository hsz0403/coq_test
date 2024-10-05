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
exact pl_tl_O.
