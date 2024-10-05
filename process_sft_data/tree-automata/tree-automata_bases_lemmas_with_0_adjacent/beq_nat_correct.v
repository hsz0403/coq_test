Require Import Bool.
Require Import Arith.
Require Import ZArith.
Require Import NArith.
Require Import Ndec.
From IntMap Require Import Allmaps.
Require Import EqNat.
Require Export Max.

Lemma beq_nat_correct : forall n : nat, beq_nat n n = true.
Proof.
simple induction n.
reflexivity.
intros.
simpl in |- *.
exact H.
