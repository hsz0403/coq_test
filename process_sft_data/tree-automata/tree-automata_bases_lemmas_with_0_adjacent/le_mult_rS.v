Require Import Bool.
Require Import Arith.
Require Import ZArith.
Require Import NArith.
Require Import Ndec.
From IntMap Require Import Allmaps.
Require Import EqNat.
Require Export Max.

Lemma le_mult_rS : forall n m : nat, n * m <= n * S m.
Proof.
intros.
cut (n * m = m * n).
cut (n * S m = S m * n).
intros.
rewrite H.
rewrite H0.
exact (le_mult_lS m n).
exact (mult_comm n (S m)).
exact (mult_comm n m).
