Require Import Bool.
Require Import Arith.
Require Import ZArith.
Require Import NArith.
Require Import Ndec.
From IntMap Require Import Allmaps.
Require Import EqNat.
Require Export Max.

Lemma le_n_n : forall n : nat, n <= n.
Proof.
simple induction n.
trivial.
intros.
exact (le_n_S n0 n0 H).
