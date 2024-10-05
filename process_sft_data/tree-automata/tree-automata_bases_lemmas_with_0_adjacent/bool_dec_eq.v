Require Import Bool.
Require Import Arith.
Require Import ZArith.
Require Import NArith.
Require Import Ndec.
From IntMap Require Import Allmaps.
Require Import EqNat.
Require Export Max.

Lemma bool_dec_eq : forall a b : bool, {a = b} + {a <> b}.
Proof.
intros.
case a.
case b.
left.
trivial.
right.
exact diff_true_false.
case b.
right.
exact diff_false_true.
left.
trivial.
