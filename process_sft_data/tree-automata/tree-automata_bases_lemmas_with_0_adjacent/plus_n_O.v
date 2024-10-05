Require Import Bool.
Require Import Arith.
Require Import ZArith.
Require Import NArith.
Require Import Ndec.
From IntMap Require Import Allmaps.
Require Import EqNat.
Require Export Max.

Lemma plus_n_O : forall n : nat, n + 0 = n.
Proof.
simple induction n.
trivial.
intros.
simpl in |- *.
rewrite H.
trivial.
