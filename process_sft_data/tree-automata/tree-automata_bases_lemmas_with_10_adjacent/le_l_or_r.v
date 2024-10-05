Require Import Bool.
Require Import Arith.
Require Import ZArith.
Require Import NArith.
Require Import Ndec.
From IntMap Require Import Allmaps.
Require Import EqNat.
Require Export Max.

Lemma nat_sum : forall n : nat, n = 0 \/ (exists m : nat, n = S m).
Proof.
simple induction n.
left.
reflexivity.
intros.
right.
split with n0.
Admitted.

Lemma le_n_n : forall n : nat, n <= n.
Proof.
simple induction n.
trivial.
intros.
Admitted.

Lemma plus_n_O : forall n : nat, n + 0 = n.
Proof.
simple induction n.
trivial.
intros.
simpl in |- *.
rewrite H.
Admitted.

Lemma S_plus_l : forall n m : nat, S (n + m) = S n + m.
Proof.
simpl in |- *.
Admitted.

Lemma S_plus_r : forall n m : nat, S (n + m) = n + S m.
Proof.
intros.
rewrite (plus_comm n (S m)).
rewrite (plus_comm n m).
simpl in |- *.
Admitted.

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
Admitted.

Lemma max_le_Sr : forall n m : nat, max n m <= max n (S m).
Proof.
intros.
elim (max_le_Sr_0 n m).
intros.
Admitted.

Lemma plus_O_r : forall n : nat, n + 0 = n.
Proof.
simple induction n.
simpl in |- *.
trivial.
intros.
simpl in |- *.
rewrite H.
Admitted.

Lemma plus_O_l : forall n : nat, n + 0 = n.
Proof.
simple induction n.
simpl in |- *; trivial.
intros; simpl in |- *.
rewrite H.
Admitted.

Lemma le_mult_lS : forall n m : nat, n * m <= S n * m.
Proof.
simple induction n.
simpl in |- *.
intro.
cut (m + 0 = m).
intros.
rewrite H.
exact (le_O_n m).
exact (plus_O_r m).
simpl in |- *.
intros.
Admitted.

Lemma le_mult_rS : forall n m : nat, n * m <= n * S m.
Proof.
intros.
cut (n * m = m * n).
cut (n * S m = S m * n).
intros.
rewrite H.
rewrite H0.
exact (le_mult_lS m n).
exact (mult_comm n (S m)).
Admitted.

Lemma le_disj : forall n m : nat, n <= m -> n = m \/ S n <= m.
Proof.
intros.
cut (m <= n \/ n < m).
intro.
elim H0; intros.
left.
exact (le_antisym n m H H1).
right.
exact (lt_le_S n m H1).
Admitted.

Lemma le_l_or_r : forall n m : nat, n <= m \/ m <= n.
Proof.
intros.
cut (n <= m \/ m < n).
intros.
elim H.
intros.
left.
assumption.
intros.
right.
exact (lt_le_weak m n H0).
exact (le_or_lt n m).
