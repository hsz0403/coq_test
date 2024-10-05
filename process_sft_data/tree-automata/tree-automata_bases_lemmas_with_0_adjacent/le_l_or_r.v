Require Import Bool.
Require Import Arith.
Require Import ZArith.
Require Import NArith.
Require Import Ndec.
From IntMap Require Import Allmaps.
Require Import EqNat.
Require Export Max.

Lemma le_l_or_r : forall n m : nat, n <= m \/ m <= n.
Proof.
intros.
cut (n <= m \/ m < n).
intros.
elim H.
intros.
left.
assumption.
intros.
right.
exact (lt_le_weak m n H0).
exact (le_or_lt n m).
