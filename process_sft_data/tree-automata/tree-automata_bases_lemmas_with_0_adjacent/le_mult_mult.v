Require Import Bool.
Require Import Arith.
Require Import ZArith.
Require Import NArith.
Require Import Ndec.
From IntMap Require Import Allmaps.
Require Import EqNat.
Require Export Max.

Lemma le_mult_mult : forall n m p q : nat, n <= m -> p <= q -> n * p <= m * q.
Proof.
intros.
cut (n * p <= n * q).
intro.
cut (n * q <= m * q).
intro.
exact (le_trans (n * p) (n * q) (m * q) H1 H2).
exact (le_mult_l n m q H).
exact (le_mult_r p q n H0).
