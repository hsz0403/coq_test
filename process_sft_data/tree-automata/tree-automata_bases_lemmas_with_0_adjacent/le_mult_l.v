Require Import Bool.
Require Import Arith.
Require Import ZArith.
Require Import NArith.
Require Import Ndec.
From IntMap Require Import Allmaps.
Require Import EqNat.
Require Export Max.

Lemma le_mult_l : forall n m p : nat, n <= m -> n * p <= m * p.
Proof.
intro.
simple induction m.
intros.
cut (n = 0).
intro.
rewrite H0; trivial.
symmetry in |- *.
exact (le_n_O_eq n H).
induction n as [| n Hrecn].
intros.
simpl in |- *.
exact (le_O_n (p + n * p)).
intros.
simpl in |- *.
cut (n = n0 \/ S n <= n0).
intro.
cut (n * p <= n0 * p).
intro.
elim H1; intros.
cut (p <= p).
intros.
exact (plus_le_compat p p (n * p) (n0 * p) H4 H2).
exact (le_n_n p).
cut (n * p <= S n * p).
cut (S n * p <= n0 * p).
intros.
apply (le_trans (p + n * p) (p + S n * p) (p + n0 * p)).
exact (plus_le_compat p p (n * p) (S n * p) (le_n_n p) H5).
exact (plus_le_compat p p (S n * p) (n0 * p) (le_n_n p) H4).
exact (H p H3).
exact (le_mult_lS n p).
elim H1; intros.
rewrite H2.
exact (le_n_n (n0 * p)).
cut (n * p <= S n * p).
intro.
cut (S n * p <= n0 * p).
intro.
exact (le_trans (n * p) (S n * p) (n0 * p) H3 H4).
exact (H p H2).
exact (le_mult_lS n p).
cut (n <= n0).
intro.
exact (le_disj n n0 H1).
exact (le_S_n n n0 H0).
