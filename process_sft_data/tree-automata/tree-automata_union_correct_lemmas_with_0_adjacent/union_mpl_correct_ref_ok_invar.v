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
exact (H0 _ _ H6 H8 _ _ H9).
