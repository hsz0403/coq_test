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
induction a1 as [| p2]; exact H4.
