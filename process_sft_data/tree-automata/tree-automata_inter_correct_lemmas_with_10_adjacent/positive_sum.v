Require Import Bool.
Require Import NArith Ndec Ndigits.
Require Import ZArith.
From IntMap Require Import Allmaps.
Require Import bases.
Require Import defs.
Require Import semantics.
Require Import signature.
Require Import refcorrect.
Require Import inter.
Definition pl_produit_ref_ok_0 (la pl : prec_list) : Prop := forall (a b : ad) (l : prec_list) (n : nat), prec_occur (pl_produit_0 a la pl n l) b -> (exists a0 : ad, (exists a1 : ad, b = iad_conv a0 a1 /\ prec_occur la a0 /\ prec_occur pl a1)) \/ (exists a1 : ad, b = iad_conv a a1 /\ prec_occur pl a1) \/ prec_occur l b.
Definition pl_produit_ref_ok_1 (p0 p1 : prec_list) : Prop := forall (b : ad) (n : nat), prec_occur (pl_produit_1 p0 n p1) b -> exists a0 : ad, (exists a1 : ad, b = iad_conv a0 a1 /\ prec_occur p0 a0 /\ prec_occur p1 a1).

Lemma pl_produit_correct_wrt_sign_invar : forall (p0 p1 : prec_list) (n : nat), pl_tl_length p0 n -> pl_tl_length p1 n -> pl_tl_length (pl_produit p0 p1) n.
Proof.
Admitted.

Lemma st_produit_l_correct_wrt_sign_invar_with_offset : forall (s0 : state) (a : ad) (p : prec_list) (sigma : signature) (pa : pre_ad), state_correct_wrt_sign_with_offset s0 sigma pa -> state_correct_wrt_sign_with_offset (M1 prec_list a p) sigma pa -> state_correct_wrt_sign_with_offset (s_produit_l a p s0) sigma pa.
Proof.
simple induction s0.
unfold state_correct_wrt_sign_with_offset in |- *.
intros.
inversion H1.
unfold state_correct_wrt_sign_with_offset in |- *.
intros.
simpl in H1.
elim (bool_is_true_or_false (N.eqb a1 a)); intros; rewrite H2 in H1.
simpl in H1.
elim (bool_is_true_or_false (N.eqb a1 a2)); intros; rewrite H3 in H1.
inversion H1.
elim (H a a0).
elim (H0 a1 p).
intros.
elim H4.
elim H6.
intros.
rewrite (Neqb_complete _ _ H2) in H9.
rewrite H9 in H7.
inversion H7.
split with x.
rewrite <- (Neqb_complete _ _ H3).
rewrite (Neqb_complete _ _ H2).
split.
exact H9.
rewrite H12 in H7.
rewrite <- H12 in H8.
exact (pl_tl_length_prod p a0 x H10 H8).
simpl in |- *.
rewrite (Neqb_correct a1).
reflexivity.
simpl in |- *.
rewrite (Neqb_correct a).
reflexivity.
inversion H1.
inversion H1.
intros.
elim (state_correct_wrt_sign_with_offset_M2 m m0 sigma pa H1).
intros.
unfold state_correct_wrt_sign_with_offset in |- *.
intros.
unfold state_correct_wrt_sign_with_offset in H.
unfold state_correct_wrt_sign_with_offset in H0.
induction a as [| p1].
induction a0 as [| p1].
simpl in H5.
elim (H N0 p sigma (pre_ad_O pa) H3) with (a := N0) (p0 := p0).
intros.
split with x.
elim H6.
intros.
split.
induction pa as [| pa Hrecpa| pa Hrecpa]; simpl in |- *; simpl in H7; exact H7.
exact H8.
intros.
elim (H2 N0 p).
intros.
split with x.
induction a as [| p2].
simpl in H6.
inversion H6.
rewrite <- H9.
simpl in |- *.
exact H7.
induction p2 as [p2 Hrecp2| p2 Hrecp2| ].
inversion H6.
inversion H6.
inversion H6.
reflexivity.
exact H5.
induction p1 as [p1 Hrecp1| p1 Hrecp1| ].
simpl in H5.
inversion H5.
simpl in H5.
elim (H N0 p sigma (pre_ad_O pa) H3) with (a := Npos p1) (p0 := p0).
intros.
split with x.
simpl in H6.
exact H6.
intros.
unfold state_correct_wrt_sign_with_offset in H2.
induction a as [| p3].
simpl in H6.
inversion H6.
elim (H2 N0 p).
intros.
split with x.
rewrite <- H8.
induction pa as [| pa Hrecpa| pa Hrecpa]; exact H7.
reflexivity.
simpl in H6.
inversion H6.
exact H5.
simpl in H5.
inversion H5.
induction p1 as [p1 Hrecp1| p1 Hrecp1| ].
clear Hrecp1.
induction a0 as [| p2].
simpl in H5.
inversion H5.
induction p2 as [p2 Hrecp2| p2 Hrecp2| ]; simpl in H5.
elim (H0 (Npos p1) p sigma (pre_ad_I pa) H4) with (a := Npos p2) (p0 := p0).
intros.
split with x.
simpl in H6.
exact H6.
intros.
unfold state_correct_wrt_sign_with_offset in H2.
induction a as [| p4].
inversion H6.
elim (H2 (Npos (xI p4)) p3).
intros.
split with x.
simpl in |- *.
exact H7.
simpl in |- *.
simpl in H6.
exact H6.
exact H5.
inversion H5.
elim (H0 (Npos p1) p sigma (pre_ad_I pa) H4) with (a := N0) (p0 := p0).
intros.
split with x.
simpl in H6.
exact H6.
intros.
induction a as [| p3].
inversion H6.
elim (H2 (Npos (xI p3)) p2).
intros.
split with x.
simpl in |- *.
exact H7.
simpl in |- *.
simpl in H6.
exact H6.
exact H5.
induction a0 as [| p2].
simpl in H5.
elim (H (Npos p1) p sigma (pre_ad_O pa) H3) with (a := N0) (p0 := p0).
intros.
split with x.
simpl in H6.
exact H6.
intros.
induction a as [| p3].
inversion H6.
elim (H2 (Npos (xO p3)) p2).
intros.
split with x.
simpl in |- *.
exact H7.
simpl in |- *.
simpl in H6.
exact H6.
exact H5.
induction p2 as [p2 Hrecp2| p2 Hrecp2| ]; simpl in H5.
inversion H5.
elim (H (Npos p1) p sigma (pre_ad_O pa) H3) with (a := Npos p2) (p0 := p0).
intros.
split with x.
simpl in H6.
exact H6.
intros.
induction a as [| p4].
inversion H6.
elim (H2 (Npos (xO p4)) p3).
intros.
split with x.
simpl in |- *.
exact H7.
simpl in |- *.
simpl in H6.
exact H6.
exact H5.
inversion H5.
induction a0 as [| p1].
simpl in H5.
inversion H5.
induction p1 as [p1 Hrecp1| p1 Hrecp1| ]; simpl in H5.
elim (H0 N0 p sigma (pre_ad_I pa) H4) with (a := Npos p1) (p0 := p0).
intros.
split with x.
simpl in H6.
exact H6.
intros.
induction a as [| p3].
elim (H2 (Npos 1) p2).
intros.
split with x.
simpl in |- *.
exact H7.
simpl in |- *.
simpl in H6.
exact H6.
inversion H6.
exact H5.
inversion H5.
elim (H0 N0 p sigma (pre_ad_I pa) H4) with (a := N0) (p0 := p0).
intros.
split with x.
simpl in H6.
exact H6.
intros.
induction a as [| p2].
elim (H2 (Npos 1) p1).
intros.
split with x.
simpl in |- *.
exact H7.
simpl in |- *.
simpl in H6.
exact H6.
inversion H6.
Admitted.

Lemma st_produit_r_correct_wrt_sign_invar_with_offset : forall (s0 : state) (a : ad) (p : prec_list) (sigma : signature) (pa : pre_ad), state_correct_wrt_sign_with_offset s0 sigma pa -> state_correct_wrt_sign_with_offset (M1 prec_list a p) sigma pa -> state_correct_wrt_sign_with_offset (s_produit_r a p s0) sigma pa.
Proof.
simple induction s0.
unfold state_correct_wrt_sign_with_offset in |- *.
intros.
inversion H1.
unfold state_correct_wrt_sign_with_offset in |- *.
intros.
simpl in H1.
elim (bool_is_true_or_false (N.eqb a1 a)); intros; rewrite H2 in H1.
simpl in H1.
elim (bool_is_true_or_false (N.eqb a1 a2)); intros; rewrite H3 in H1.
inversion H1.
elim (H a a0).
elim (H0 a1 p).
intros.
elim H4.
elim H6.
intros.
rewrite (Neqb_complete _ _ H2) in H9.
rewrite H9 in H7.
inversion H7.
split with x.
rewrite <- (Neqb_complete _ _ H3).
rewrite (Neqb_complete _ _ H2).
split.
exact H9.
rewrite H12 in H7.
rewrite <- H12 in H8.
exact (pl_tl_length_prod a0 p x H8 H10).
simpl in |- *.
rewrite (Neqb_correct a1).
reflexivity.
simpl in |- *.
rewrite (Neqb_correct a).
reflexivity.
inversion H1.
inversion H1.
intros.
elim (state_correct_wrt_sign_with_offset_M2 m m0 sigma pa H1).
intros.
unfold state_correct_wrt_sign_with_offset in |- *.
intros.
unfold state_correct_wrt_sign_with_offset in H.
unfold state_correct_wrt_sign_with_offset in H0.
induction a as [| p1].
induction a0 as [| p1].
simpl in H5.
elim (H N0 p sigma (pre_ad_O pa) H3) with (a := N0) (p0 := p0).
intros.
split with x.
simpl in H6.
exact H6.
intros.
elim (H2 N0 p1).
intros.
split with x.
simpl in |- *.
induction a as [| p2].
exact H7.
inversion H6.
induction a as [| p2].
exact H6.
inversion H6.
exact H5.
induction p1 as [p1 Hrecp1| p1 Hrecp1| ]; simpl in H5.
inversion H5.
elim (H N0 p sigma (pre_ad_O pa) H3) with (a := Npos p1) (p0 := p0).
intros.
split with x.
simpl in H6.
exact H6.
intros.
induction a as [| p3].
elim (H2 N0 p2).
intros.
split with x.
simpl in |- *.
exact H7.
exact H6.
inversion H6.
exact H5.
inversion H5.
induction p1 as [p1 Hrecp1| p1 Hrecp1| ].
induction a0 as [| p2].
simpl in H5.
inversion H5.
induction p2 as [p2 Hrecp2| p2 Hrecp2| ]; simpl in H5.
elim (H0 (Npos p1) p sigma (pre_ad_I pa) H4) with (a := Npos p2) (p0 := p0).
intros.
split with x.
simpl in H6.
exact H6.
intros.
induction a as [| p4].
inversion H6.
elim (H2 (Npos (xI p4)) p3).
intros.
split with x.
simpl in |- *.
exact H7.
simpl in |- *.
simpl in H6.
exact H6.
exact H5.
inversion H5.
elim (H0 (Npos p1) p sigma (pre_ad_I pa) H4) with (a := N0) (p0 := p0).
intros.
split with x.
exact H6.
intros.
induction a as [| p3].
inversion H6.
elim (H2 (Npos (xI p3)) p2).
intros.
split with x.
simpl in |- *.
exact H7.
simpl in |- *.
exact H6.
exact H5.
induction a0 as [| p2].
simpl in H5.
elim (H (Npos p1) p sigma (pre_ad_O pa) H3) with (a := N0) (p0 := p0).
intros.
split with x.
simpl in H6.
exact H6.
intros.
induction a as [| p3].
inversion H6.
elim (H2 (Npos (xO p3)) p2).
intros.
split with x.
simpl in |- *.
exact H7.
simpl in |- *.
simpl in H6.
exact H6.
exact H5.
induction p2 as [p2 Hrecp2| p2 Hrecp2| ]; simpl in H5.
inversion H5.
elim (H (Npos p1) p sigma (pre_ad_O pa) H3) with (a := Npos p2) (p0 := p0).
intros.
split with x.
simpl in H6.
exact H6.
intros.
induction a as [| p4].
inversion H6.
elim (H2 (Npos (xO p4)) p3).
intros.
split with x.
simpl in |- *.
exact H7.
simpl in |- *.
simpl in H6.
exact H6.
exact H5.
inversion H5.
induction a0 as [| p1].
simpl in H5.
inversion H5.
induction p1 as [p1 Hrecp1| p1 Hrecp1| ]; simpl in H5.
elim (H0 N0 p sigma (pre_ad_I pa) H4) with (a := Npos p1) (p0 := p0).
intros.
split with x.
simpl in H6.
exact H6.
intros.
induction a as [| p3].
elim (H2 (Npos 1) p2).
intros.
split with x.
simpl in |- *.
exact H7.
simpl in |- *.
simpl in H6.
exact H6.
inversion H6.
exact H5.
inversion H5.
elim (H0 N0 p sigma (pre_ad_I pa) H4) with (a := N0) (p0 := p0).
intros.
split with x.
simpl in H6.
exact H6.
intros.
induction a as [| p2].
elim (H2 (Npos 1) p1).
intros.
split with x.
simpl in |- *.
exact H7.
simpl in |- *.
simpl in H6.
exact H6.
inversion H6.
Admitted.

Lemma st_produit_correct_wrt_sign_invar_with_offset : forall (s0 s1 : state) (sigma : signature) (pa : pre_ad), state_correct_wrt_sign_with_offset s0 sigma pa -> state_correct_wrt_sign_with_offset s1 sigma pa -> state_correct_wrt_sign_with_offset (s_produit s0 s1) sigma pa.
Proof.
simple induction s0.
simple induction s1.
intros.
simpl in |- *.
unfold state_correct_wrt_sign_with_offset in |- *.
intros.
inversion H1.
intros.
simpl in |- *.
unfold state_correct_wrt_sign_with_offset in |- *.
intros.
inversion H1.
intros.
simpl in |- *.
unfold state_correct_wrt_sign_with_offset in |- *.
intros.
inversion H3.
simple induction s1.
simpl in |- *.
intros.
unfold state_correct_wrt_sign_with_offset in |- *.
intros.
inversion H1.
intros.
replace (s_produit (M1 prec_list a a0) (M1 prec_list a1 a2)) with (s_produit_l a a0 (M1 prec_list a1 a2)).
exact (st_produit_l_correct_wrt_sign_invar_with_offset (M1 prec_list a1 a2) a a0 sigma pa H0 H).
reflexivity.
intros.
replace (s_produit (M1 prec_list a a0) (M2 prec_list m m0)) with (s_produit_l a a0 (M2 prec_list m m0)).
exact (st_produit_l_correct_wrt_sign_invar_with_offset (M2 prec_list m m0) a a0 sigma pa H2 H1).
reflexivity.
simple induction s1.
simpl in |- *.
intros.
exact H2.
intros.
replace (s_produit (M2 prec_list m m0) (M1 prec_list a a0)) with (s_produit_r a a0 (M2 prec_list m m0)).
exact (st_produit_r_correct_wrt_sign_invar_with_offset (M2 prec_list m m0) a a0 sigma pa H1 H2).
reflexivity.
intros.
unfold state_correct_wrt_sign_with_offset in |- *.
simpl in |- *.
intros.
elim (state_correct_wrt_sign_with_offset_M2 _ _ _ _ H3).
intros.
elim (state_correct_wrt_sign_with_offset_M2 _ _ _ _ H4).
intros.
induction a as [| p0].
exact (H _ _ _ H6 H8 N0 p H5).
induction p0 as [p0 Hrecp0| p0 Hrecp0| ].
exact (H0 _ _ _ H7 H9 (Npos p0) p H5).
exact (H _ _ _ H6 H8 _ _ H5).
Admitted.

Lemma st_produit_correct_wrt_sign_invar : forall (s0 s1 : state) (sigma : signature), state_correct_wrt_sign s0 sigma -> state_correct_wrt_sign s1 sigma -> state_correct_wrt_sign (s_produit s0 s1) sigma.
Proof.
intros.
replace (state_correct_wrt_sign (s_produit s0 s1) sigma) with (state_correct_wrt_sign_with_offset (s_produit s0 s1) sigma pre_ad_empty).
apply (st_produit_correct_wrt_sign_invar_with_offset s0 s1 sigma pre_ad_empty).
unfold state_correct_wrt_sign_with_offset in |- *.
simpl in |- *.
exact H.
unfold state_correct_wrt_sign_with_offset in |- *.
simpl in |- *.
exact H0.
Admitted.

Lemma preDTA_produit_l_correct_wrt_sign_invar : forall (d : preDTA) (a : ad) (s : state) (sigma : signature), predta_correct_wrt_sign d sigma -> predta_correct_wrt_sign (M1 state a s) sigma -> predta_correct_wrt_sign (preDTA_produit_l a s d) sigma.
Proof.
simple induction d.
intros.
simpl in |- *.
exact H.
simpl in |- *.
unfold predta_correct_wrt_sign in |- *.
intros.
simpl in H1.
elim (bool_is_true_or_false (N.eqb (iad_conv a1 a) a2)); intros; rewrite H2 in H1.
inversion H1.
apply (st_produit_correct_wrt_sign_invar s a0 sigma).
apply (H0 a1 s).
simpl in |- *.
rewrite (Neqb_correct a1).
reflexivity.
apply (H a a0).
simpl in |- *.
rewrite (Neqb_correct a).
reflexivity.
inversion H1.
intros.
elim (predta_correct_wrt_sign_M2 m m0 sigma H1).
intros.
induction a as [| p].
simpl in |- *.
unfold predta_correct_wrt_sign in |- *.
intros.
induction a as [| p].
simpl in H5.
exact (H N0 s sigma H3 H2 N0 s0 H5).
elim (positive_sum p); intros.
rewrite H6 in H5.
simpl in H5.
inversion H5.
elim H6.
intros.
elim H7.
intros.
rewrite H8 in H5.
simpl in H5.
elim (positive_sum x).
intros.
rewrite H9 in H5.
exact (H0 N0 s sigma H4 H2 N0 s0 H5).
intros.
elim H9.
intros.
elim H10.
intros.
rewrite H11 in H5.
exact (H N0 s sigma H3 H2 (Npos x0) s0 H5).
intros.
elim H10.
intros.
rewrite H11 in H5.
exact (H0 N0 s sigma H4 H2 (Npos x0) s0 H5).
intros.
elim H7.
intros.
rewrite H8 in H5.
simpl in H5.
inversion H5.
induction p as [p Hrecp| p Hrecp| ].
cut (predta_correct_wrt_sign (M1 state (Npos p) s) sigma).
intros.
unfold predta_correct_wrt_sign in |- *.
intros.
simpl in H6.
induction a as [| p0].
inversion H6.
elim (positive_sum p0); intros.
rewrite H7 in H6.
exact (H (Npos p) s sigma H3 H5 N0 s0 H6).
elim H7; intros; elim H8; intros; rewrite H9 in H6.
inversion H6.
elim (positive_sum x).
intros.
rewrite H10 in H6.
exact (H0 (Npos p) s _ H4 H5 _ _ H6).
intros.
elim H10; intros; elim H11; intros; rewrite H12 in H6.
exact (H _ _ _ H3 H5 _ _ H6).
exact (H0 _ _ _ H4 H5 _ _ H6).
unfold predta_correct_wrt_sign in |- *.
simple induction a.
exact (H2 (Npos 1)).
intro.
exact (H2 (Npos (xI p0))).
cut (predta_correct_wrt_sign (M1 state (Npos p) s) sigma).
intro.
unfold predta_correct_wrt_sign in |- *.
intros.
simpl in H6.
induction a as [| p0].
exact (H _ _ _ H3 H5 _ _ H6).
elim (positive_sum p0); intros.
rewrite H7 in H6.
inversion H6.
elim H7; intros; elim H8; intros; rewrite H9 in H6.
elim (positive_sum x); intros.
rewrite H10 in H6.
exact (H0 _ _ _ H4 H5 _ _ H6).
elim H10; intros; elim H11; intros; rewrite H12 in H6.
exact (H _ _ _ H3 H5 _ _ H6).
exact (H0 _ _ _ H4 H5 _ _ H6).
inversion H6.
unfold predta_correct_wrt_sign in |- *.
simple induction a.
exact (H2 N0).
intro.
exact (H2 (Npos (xO p0))).
cut (predta_correct_wrt_sign (M1 state N0 s) sigma).
intros.
unfold predta_correct_wrt_sign in |- *.
intros.
simpl in H6.
induction a as [| p].
inversion H6.
elim (positive_sum p); intros.
rewrite H7 in H6.
exact (H _ _ _ H3 H5 _ _ H6).
elim H7; intros; elim H8; intros; rewrite H9 in H6.
inversion H6.
elim (positive_sum x); intros.
rewrite H10 in H6.
exact (H0 _ _ _ H4 H5 _ _ H6).
elim H10; intros; elim H11; intros; rewrite H12 in H6.
exact (H _ _ _ H3 H5 _ _ H6).
exact (H0 _ _ _ H4 H5 _ _ H6).
unfold predta_correct_wrt_sign in |- *.
simple induction a.
exact (H2 (Npos 1)).
intro.
Admitted.

Lemma preDTA_produit_r_correct_wrt_sign_invar : forall (d : preDTA) (a : ad) (s : state) (sigma : signature), predta_correct_wrt_sign d sigma -> predta_correct_wrt_sign (M1 state a s) sigma -> predta_correct_wrt_sign (preDTA_produit_r a s d) sigma.
Proof.
simple induction d.
intros.
simpl in |- *.
exact H.
unfold predta_correct_wrt_sign in |- *.
intros.
simpl in H1.
elim (bool_is_true_or_false (N.eqb (iad_conv a a1) a2)); intros; rewrite H2 in H1.
inversion H1.
apply (st_produit_correct_wrt_sign_invar a0 s sigma).
apply (H a a0).
simpl in |- *.
rewrite (Neqb_correct a).
reflexivity.
apply (H0 a1 s).
simpl in |- *.
rewrite (Neqb_correct a1).
reflexivity.
inversion H1.
intros.
elim (predta_correct_wrt_sign_M2 m m0 sigma H1).
intros.
induction a as [| p].
simpl in |- *.
unfold predta_correct_wrt_sign in |- *.
intros.
simpl in H5.
induction a as [| p].
exact (H _ _ _ H3 H2 _ _ H5).
elim (positive_sum p); intros.
rewrite H6 in H5.
exact (H0 _ _ _ H4 H2 _ _ H5).
elim H6; intros; elim H7; intros; rewrite H8 in H5.
elim (positive_sum x); intros.
rewrite H9 in H5.
inversion H5.
elim H9; intros; elim H10; intros; rewrite H11 in H5.
exact (H _ _ _ H3 H2 _ _ H5).
inversion H5.
elim (positive_sum x); intros.
rewrite H9 in H5.
inversion H5.
elim H9; intros; elim H10; intros; rewrite H11 in H5.
exact (H0 _ _ _ H4 H2 _ _ H5).
inversion H5.
induction p as [p Hrecp| p Hrecp| ].
cut (predta_correct_wrt_sign (M1 state (Npos p) s) sigma).
intros.
unfold predta_correct_wrt_sign in |- *.
intros.
simpl in H6.
induction a as [| p0].
inversion H6.
elim (positive_sum p0); intros.
rewrite H7 in H6.
inversion H6.
elim H7; intros; elim H8; intros; rewrite H9 in H6.
elim (positive_sum x); intros.
rewrite H10 in H6.
exact (H _ _ _ H3 H5 _ _ H6).
elim H10; intros; elim H11; intros; rewrite H12 in H6.
inversion H6.
exact (H _ _ _ H3 H5 _ _ H6).
elim (positive_sum x); intros.
rewrite H10 in H6.
exact (H0 _ _ _ H4 H5 _ _ H6).
elim H10; intros; elim H11; intros; rewrite H12 in H6.
inversion H6.
exact (H0 _ _ _ H4 H5 _ _ H6).
unfold predta_correct_wrt_sign in |- *.
simple induction a.
exact (H2 (Npos 1)).
intro.
exact (H2 (Npos (xI p0))).
cut (predta_correct_wrt_sign (M1 state (Npos p) s) sigma).
intro.
unfold predta_correct_wrt_sign in |- *.
intros.
simpl in H6.
induction a as [| p0].
exact (H _ _ _ H3 H5 _ _ H6).
elim (positive_sum p0); intros.
rewrite H7 in H6.
exact (H0 _ _ _ H4 H5 _ _ H6).
elim H7; intros; elim H8; intros; rewrite H9 in H6.
elim (positive_sum x); intros.
rewrite H10 in H6.
inversion H6.
elim H10; intros; elim H11; intros; rewrite H12 in H6.
exact (H _ _ _ H3 H5 _ _ H6).
inversion H6.
elim (positive_sum x); intros.
rewrite H10 in H6.
inversion H6.
elim H10; intros; elim H11; intros; rewrite H12 in H6.
exact (H0 _ _ _ H4 H5 _ _ H6).
inversion H6.
unfold predta_correct_wrt_sign in |- *.
simple induction a.
exact (H2 N0).
intro.
exact (H2 (Npos (xO p0))).
cut (predta_correct_wrt_sign (M1 state N0 s) sigma).
intro.
unfold predta_correct_wrt_sign in |- *.
intros.
simpl in H6.
induction a as [| p].
inversion H6.
elim (positive_sum p); intros.
rewrite H7 in H6.
inversion H6.
elim H7; intros; elim H8; intros; rewrite H9 in H6.
elim (positive_sum x); intros.
rewrite H10 in H6.
exact (H _ _ _ H3 H5 _ _ H6).
elim H10; intros; elim H11; intros; rewrite H12 in H6.
inversion H6.
exact (H _ _ _ H3 H5 _ _ H6).
elim (positive_sum x); intros.
rewrite H10 in H6.
exact (H0 _ _ _ H4 H5 _ _ H6).
elim H10; intros; elim H11; intros; rewrite H12 in H6.
inversion H6.
exact (H0 _ _ _ H4 H5 _ _ H6).
unfold predta_correct_wrt_sign in |- *.
simple induction a.
exact (H2 (Npos 1)).
intro.
Admitted.

Lemma preDTA_produit_correct_wrt_sign_invar : forall (d0 d1 : preDTA) (sigma : signature), predta_correct_wrt_sign d0 sigma -> predta_correct_wrt_sign d1 sigma -> predta_correct_wrt_sign (preDTA_produit d0 d1) sigma.
Proof.
simple induction d0.
simple induction d1.
simpl in |- *.
intros.
exact H.
simpl in |- *.
intros.
exact H.
intros.
simpl in |- *.
exact H1.
simple induction d1.
simpl in |- *.
intros.
exact H0.
intros.
replace (preDTA_produit (M1 state a a0) (M1 state a1 a2)) with (preDTA_produit_l a a0 (M1 state a1 a2)).
exact (preDTA_produit_l_correct_wrt_sign_invar (M1 state a1 a2) a a0 sigma H0 H).
reflexivity.
intros.
replace (preDTA_produit (M1 state a a0) (M2 state m m0)) with (preDTA_produit_l a a0 (M2 state m m0)).
exact (preDTA_produit_l_correct_wrt_sign_invar (M2 state m m0) a a0 sigma H2 H1).
reflexivity.
simple induction d1.
simpl in |- *.
intros.
exact H2.
intros.
replace (preDTA_produit (M2 state m m0) (M1 state a a0)) with (preDTA_produit_r a a0 (M2 state m m0)).
exact (preDTA_produit_r_correct_wrt_sign_invar (M2 state m m0) a a0 sigma H1 H2).
reflexivity.
intros.
simpl in |- *.
elim (predta_correct_wrt_sign_M2 _ _ _ H3).
intros.
elim (predta_correct_wrt_sign_M2 _ _ _ H4).
intros.
unfold predta_correct_wrt_sign in |- *.
intros.
simpl in H9.
induction a as [| p].
exact (H _ _ H5 H7 N0 s H9).
elim (positive_sum p); intros.
rewrite H10 in H9.
exact (H0 _ _ H6 H7 _ _ H9).
elim H10; intros; elim H11; intros; rewrite H12 in H9.
elim (positive_sum x); intros.
rewrite H13 in H9.
exact (H _ _ H5 H8 _ _ H9).
elim H13; intros; elim H14; intros; rewrite H15 in H9.
exact (H _ _ H5 H7 _ _ H9).
exact (H _ _ H5 H8 _ _ H9).
elim (positive_sum x); intros.
rewrite H13 in H9.
exact (H0 _ _ H6 H8 _ _ H9).
elim H13; intros; elim H14; intros; rewrite H15 in H9.
exact (H0 _ _ H6 H7 _ _ H9).
Admitted.

Lemma inter_correct_wrt_sign_invar : forall (d0 d1 : DTA) (sigma : signature), dta_correct_wrt_sign d0 sigma -> dta_correct_wrt_sign d1 sigma -> dta_correct_wrt_sign (inter d0 d1) sigma.
Proof.
simple induction d0.
simple induction d1.
simpl in |- *.
intros.
Admitted.

Lemma pl_produit_ref_ok_lem_0 : forall p : prec_list, pl_produit_ref_ok_0 p prec_empty.
Proof.
unfold pl_produit_ref_ok_0 in |- *.
intros.
induction p as [a0 p1 Hrecp1 p0 Hrecp0| ].
induction n as [| n Hrecn].
simpl in H.
inversion H.
simpl in H.
right.
right.
exact H.
induction n as [| n Hrecn].
simpl in H.
inversion H.
simpl in H.
right.
right.
Admitted.

Lemma pl_produit_ref_ok_lem_1 : forall p : prec_list, pl_produit_ref_ok_1 p prec_empty.
Proof.
unfold pl_produit_ref_ok_1 in |- *.
intros.
induction n as [| n Hrecn].
simpl in H.
inversion H.
simpl in H.
Admitted.

Lemma pl_produit_ref_ok_lem_2 : forall p : prec_list, pl_produit_ref_ok_1 prec_empty p.
Proof.
unfold pl_produit_ref_ok_1 in |- *.
intros.
induction n as [| n Hrecn].
inversion H.
Admitted.

Lemma pl_produit_ref_ok_lem_3 : forall (a : ad) (la ls p : prec_list), pl_produit_ref_ok_0 p ls -> pl_produit_ref_ok_1 p la -> pl_produit_ref_ok_0 p (prec_cons a la ls).
Proof.
unfold pl_produit_ref_ok_0, pl_produit_ref_ok_1 in |- *.
intros.
elim (nat_sum n); intros.
rewrite H2 in H1.
inversion H1.
elim H2.
intros.
rewrite H3 in H1.
cut (pl_produit_0 a0 p (prec_cons a la ls) (S x) l = prec_cons (iad_conv a0 a) (pl_produit_1 p x la) (pl_produit_0 a0 p ls x l)).
intros.
rewrite H4 in H1.
inversion H1.
right.
left.
split with a.
split.
reflexivity.
exact (prec_hd a la ls).
left.
elim (H0 b x H9).
intros.
elim H10.
intros.
elim H11.
intros.
elim H12.
intros.
elim H13.
intros.
split with x0.
split with x1.
split.
exact H12.
split.
exact H14.
exact (prec_int0 a x1 la ls H15).
elim (H _ _ _ _ H9).
intros.
left.
elim H10.
intros.
elim H11.
intros.
elim H12.
intros.
elim H14.
intros.
split with x0.
split with x1.
split.
exact H13.
split.
exact H15.
exact (prec_int1 a _ la _ H16).
intros.
elim H10.
intros.
right.
left.
elim H11.
intros.
elim H12.
intros.
split with x0.
split.
exact H13.
exact (prec_int1 a _ la _ H14).
intros.
right.
right.
exact H11.
Admitted.

Lemma pl_produit_ref_ok_lem_4 : forall (a : ad) (la ls p : prec_list), pl_produit_ref_ok_0 la p -> pl_produit_ref_ok_1 ls p -> pl_produit_ref_ok_1 (prec_cons a la ls) p.
Proof.
unfold pl_produit_ref_ok_0, pl_produit_ref_ok_1 in |- *.
intros.
elim (nat_sum n); intros.
rewrite H2 in H1.
inversion H1.
elim H2.
intros.
rewrite H3 in H1.
elim (pl_sum p).
intros.
rewrite H4 in H1.
inversion H1.
intros.
elim H4.
intros.
elim H5.
intros.
elim H6.
intros.
rewrite H7 in H1.
cut (pl_produit_1 (prec_cons a la ls) (S x) (prec_cons x0 x1 x2) = pl_produit_0 a la (prec_cons x0 x1 x2) x (pl_produit_1 ls x (prec_cons x0 x1 x2))).
intro.
rewrite H8 in H1.
rewrite <- H7 in H1.
elim (H _ _ _ _ H1).
intros.
elim H9.
intros.
elim H10.
intros.
elim H11.
intros.
elim H13.
intros.
split with x3.
split with x4.
split.
exact H12.
split.
exact (prec_int0 a x3 la ls H14).
exact H15.
intros.
elim H9.
intros.
elim H10.
intros.
elim H11.
intros.
split with a.
split with x3.
split.
exact H12.
split.
exact (prec_hd a la ls).
exact H13.
intros.
elim (H0 _ _ H10).
intros.
elim H11.
intros.
elim H12.
intros.
elim H14.
intros.
split with x3.
split with x4.
split.
exact H13.
split.
exact (prec_int1 a _ la _ H15).
exact H16.
Admitted.

Lemma pl_produit_ref_ok_lem_5 : forall p p' : prec_list, pl_produit_ref_ok_0 p p' /\ pl_produit_ref_ok_1 p p'.
Proof.
Admitted.

Lemma positive_sum : forall p : positive, p = 1%positive \/ (exists q : positive, p = xO q) \/ (exists q : positive, p = xI q).
Proof.
simple induction p.
intros.
right.
right.
split with p0.
reflexivity.
intros.
right.
left.
split with p0.
reflexivity.
left.
reflexivity.
