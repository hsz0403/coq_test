Require Import Bool.
Require Import Arith.
Require Import ZArith.
Require Import NArith.
Require Import Ndec.
From IntMap Require Import Allmaps.
Require Import EqNat.
Require Export Max.

Lemma aux_Neqb_1_0 : forall p : positive, Pos.eqb p p = true.
Proof.
simple induction p.
simpl in |- *.
intros.
trivial.
simpl in |- *.
intros.
trivial.
trivial.
