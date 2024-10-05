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
exact pl_tl_O.
