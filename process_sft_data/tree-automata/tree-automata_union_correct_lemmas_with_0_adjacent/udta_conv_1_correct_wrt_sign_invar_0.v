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
exact H2.
