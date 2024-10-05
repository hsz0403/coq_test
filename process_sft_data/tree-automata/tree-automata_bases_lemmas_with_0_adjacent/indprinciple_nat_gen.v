Require Import Bool.
Require Import Arith.
Require Import ZArith.
Require Import NArith.
Require Import Ndec.
From IntMap Require Import Allmaps.
Require Import EqNat.
Require Export Max.

Lemma indprinciple_nat_gen : forall P : nat -> Prop, (forall n : nat, (forall m : nat, m < n -> P m) -> P n) -> forall n m : nat, m <= n -> P m.
Proof.
intro.
intro.
simple induction n.
intros.
apply (H m).
intros.
elim (lt_n_O m0 (lt_le_trans m0 m 0 H1 H0)).
intros.
elim (le_lt_or_eq m (S n0) H1).
intros.
exact (H0 m (lt_n_Sm_le m n0 H2)).
intro.
rewrite H2.
apply (H (S n0)).
intros.
exact (H0 m0 (lt_n_Sm_le m0 n0 H3)).
