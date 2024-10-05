Require Import Bool.
Require Import Arith.
Require Import ZArith.
Require Import NArith.
Require Import Ndec.
From IntMap Require Import Allmaps.
Require Import EqNat.
Require Export Max.

Lemma le_mult_r : forall n m p : nat, n <= m -> p * n <= p * m.
Proof.
intros.
cut (p * n = n * p).
intros.
cut (p * m = m * p).
intros.
rewrite H0.
rewrite H1.
exact (le_mult_l n m p H).
exact (mult_comm p m).
exact (mult_comm p n).
