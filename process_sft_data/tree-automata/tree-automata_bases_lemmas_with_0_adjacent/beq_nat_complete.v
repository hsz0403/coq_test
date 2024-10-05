Require Import Bool.
Require Import Arith.
Require Import ZArith.
Require Import NArith.
Require Import Ndec.
From IntMap Require Import Allmaps.
Require Import EqNat.
Require Export Max.

Lemma beq_nat_complete : forall n m : nat, beq_nat n m = true -> n = m.
Proof.
simple induction n.
simple induction m.
intros.
reflexivity.
intros.
inversion H0.
simple induction m.
intros.
inversion H0.
intros.
simpl in H1.
rewrite (H _ H1).
reflexivity.
