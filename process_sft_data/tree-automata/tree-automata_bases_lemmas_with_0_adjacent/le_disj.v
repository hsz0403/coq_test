Require Import Bool.
Require Import Arith.
Require Import ZArith.
Require Import NArith.
Require Import Ndec.
From IntMap Require Import Allmaps.
Require Import EqNat.
Require Export Max.

Lemma le_disj : forall n m : nat, n <= m -> n = m \/ S n <= m.
Proof.
intros.
cut (m <= n \/ n < m).
intro.
elim H0; intros.
left.
exact (le_antisym n m H H1).
right.
exact (lt_le_S n m H1).
exact (le_or_lt m n).
