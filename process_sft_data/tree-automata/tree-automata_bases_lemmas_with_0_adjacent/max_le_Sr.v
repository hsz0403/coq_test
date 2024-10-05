Require Import Bool.
Require Import Arith.
Require Import ZArith.
Require Import NArith.
Require Import Ndec.
From IntMap Require Import Allmaps.
Require Import EqNat.
Require Export Max.

Lemma max_le_Sr : forall n m : nat, max n m <= max n (S m).
Proof.
intros.
elim (max_le_Sr_0 n m).
intros.
exact H.
