Require Import Bool.
Require Import Arith.
Require Import ZArith.
Require Import NArith.
Require Import Ndec.
From IntMap Require Import Allmaps.
Require Import EqNat.
Require Export Max.

Lemma bool_is_false_or_true : forall a : bool, a = false \/ a = true.
Proof.
simple induction a.
right.
trivial.
left.
trivial.
