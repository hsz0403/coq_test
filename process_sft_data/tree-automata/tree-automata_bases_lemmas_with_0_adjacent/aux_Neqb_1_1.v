Require Import Bool.
Require Import Arith.
Require Import ZArith.
Require Import NArith.
Require Import Ndec.
From IntMap Require Import Allmaps.
Require Import EqNat.
Require Export Max.

Lemma aux_Neqb_1_1 : forall p p0 : positive, Pos.eqb p p0 = true -> p = p0.
Proof.
simple induction p.
intro.
intro.
simple induction p1.
intros.
simpl in H1.
cut (p0 = p2).
intro.
rewrite H2.
trivial.
exact (H p2 H1).
intros.
simpl in H1.
inversion H1.
intros.
inversion H0.
intro.
intro.
simple induction p1.
intros.
inversion H1.
intros.
cut (p0 = p2).
intros.
rewrite H2.
trivial.
simpl in H1.
exact (H p2 H1).
intros.
inversion H0.
simple induction p0.
intros.
inversion H0.
intros.
inversion H0.
intros.
trivial.
