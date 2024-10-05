Require Import Bool.
Require Import Arith.
Require Import ZArith.
Require Import NArith.
Require Import Ndec.
From IntMap Require Import Allmaps.
Require Import EqNat.
Require Export Max.

Lemma S_plus_r : forall n m : nat, S (n + m) = n + S m.
Proof.
intros.
rewrite (plus_comm n (S m)).
rewrite (plus_comm n m).
simpl in |- *.
trivial.
