Require Import Bool.
Require Import Arith.
Require Import ZArith.
Require Import NArith.
Require Import Ndec.
From IntMap Require Import Allmaps.
Require Import EqNat.
Require Export Max.

Lemma nat_sum : forall n : nat, n = 0 \/ (exists m : nat, n = S m).
Proof.
simple induction n.
left.
reflexivity.
intros.
right.
split with n0.
reflexivity.
