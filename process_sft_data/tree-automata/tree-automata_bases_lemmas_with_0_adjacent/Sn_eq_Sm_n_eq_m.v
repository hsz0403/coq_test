Require Import Bool.
Require Import Arith.
Require Import ZArith.
Require Import NArith.
Require Import Ndec.
From IntMap Require Import Allmaps.
Require Import EqNat.
Require Export Max.

Lemma Sn_eq_Sm_n_eq_m : forall n m : nat, S n = S m -> n = m.
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
inversion H1.
reflexivity.
