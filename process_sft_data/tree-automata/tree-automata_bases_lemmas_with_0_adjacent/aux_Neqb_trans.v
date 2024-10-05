Require Import Bool.
Require Import Arith.
Require Import ZArith.
Require Import NArith.
Require Import Ndec.
From IntMap Require Import Allmaps.
Require Import EqNat.
Require Export Max.

Lemma aux_Neqb_trans : forall a b c : ad, N.eqb a b = true -> N.eqb b c = true -> N.eqb a c = true.
Proof.
intros.
rewrite <- (Neqb_complete b c H0).
trivial.
