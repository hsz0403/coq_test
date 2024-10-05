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
exact H5.
