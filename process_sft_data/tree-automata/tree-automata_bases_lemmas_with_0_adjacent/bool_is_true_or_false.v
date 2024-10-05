Require Import Bool.
Require Import Arith.
Require Import ZArith.
Require Import NArith.
Require Import Ndec.
From IntMap Require Import Allmaps.
Require Import EqNat.
Require Export Max.

Lemma bool_is_true_or_false : forall a : bool, a = true \/ a = false.
Proof.
simple induction a.
left.
trivial.
right.
trivial.
