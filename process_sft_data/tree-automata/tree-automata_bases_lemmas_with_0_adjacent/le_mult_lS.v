Require Import Bool.
Require Import Arith.
Require Import ZArith.
Require Import NArith.
Require Import Ndec.
From IntMap Require Import Allmaps.
Require Import EqNat.
Require Export Max.

Lemma le_mult_lS : forall n m : nat, n * m <= S n * m.
Proof.
simple induction n.
simpl in |- *.
intro.
cut (m + 0 = m).
intros.
rewrite H.
exact (le_O_n m).
exact (plus_O_r m).
simpl in |- *.
intros.
exact (le_plus_r m (m + n0 * m)).
