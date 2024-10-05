Require Import Bool.
Require Import Arith.
Require Import ZArith.
Require Import NArith.
Require Import Ndec.
From IntMap Require Import Allmaps.
Require Import EqNat.
Require Export Max.

Lemma max_le_Sr_0 : forall n m : nat, max n m <= max n (S m) /\ max (S n) m <= max (S n) (S m).
Proof.
simple induction n; simple induction m.
simpl in |- *.
split.
exact (le_n_Sn 0).
exact (le_n_n 1).
intros.
split.
elim H.
intros.
intros.
simpl in |- *.
exact (le_n_Sn (S n0)).
elim H.
intros.
simpl in |- *.
exact (le_n_Sn (S n0)).
split.
simpl in |- *.
cut (max n0 0 = n0).
intros.
rewrite H0.
trivial.
rewrite max_l; auto with arith.
simpl in |- *.
exact (le_n_n (S (S n0))).
intros.
elim H0.
intros.
split.
simpl in |- *.
elim (H n1).
intros.
exact (le_n_S (max n0 n1) (max n0 (S n1)) H3).
cut (max (S (S n0)) (S n1) = S (max (S n0) n1)).
cut (max (S (S n0)) (S (S n1)) = S (max (S n0) (S n1))).
intros.
rewrite H3.
rewrite H4.
elim (H (S n1)).
intros.
elim (H n1).
intros.
exact (le_n_S (max (S n0) n1) (max (S n0) (S n1)) H8).
simpl in |- *.
trivial.
simpl in |- *.
trivial.
