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
exact (H0 a H1).
