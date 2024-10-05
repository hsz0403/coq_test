Require Import Bool.
Require Import Arith.
Require Import ZArith.
Require Import NArith.
Require Import Ndec.
From IntMap Require Import Allmaps.
Require Import EqNat.
Require Export Max.

Lemma S_plus_l : forall n m : nat, S (n + m) = S n + m.
Proof.
simpl in |- *.
trivial.
