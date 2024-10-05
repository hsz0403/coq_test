Require Import Bool.
Require Import Arith.
Require Import ZArith.
Require Import NArith.
Require Import Ndec.
From IntMap Require Import Allmaps.
Require Import EqNat.
Require Export Max.

Lemma in_M0_false : forall (A : Set) (a : A), ~ (exists e : ad, MapGet A (M0 A) e = Some a).
Proof.
intros.
intro.
elim H.
intros.
inversion H0.
