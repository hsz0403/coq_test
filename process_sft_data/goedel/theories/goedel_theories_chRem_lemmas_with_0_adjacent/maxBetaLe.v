Require Import Arith.
Require Import Wf_nat.
Require Import ZArith.
Require Import Peano_dec.
Require Import ZArith_dec.
From Pocklington Require Import gcd divides natZ prime modprime.
Require Import Max.
Definition CoPrime (a b : nat) := gcd (Z_of_nat a) (Z_of_nat b) 1.
Definition prod : forall (n : nat) (x : nat -> nat), nat.
intros.
induction n as [| n Hrecn].
exact 1.
exact (x n * Hrecn).
Defined.
Definition factorial (n : nat) : nat := prod n S.
Definition coPrimeBeta (z c : nat) : nat := S (c * S z).
Definition maxBeta (n : nat) (x : nat -> nat) : nat.
intros.
induction n as [| n Hrecn].
exact 0.
exact (max (x n) Hrecn).
Defined.

Lemma maxBetaLe : forall (n : nat) (x : nat -> nat) (i : nat), i < n -> x i <= maxBeta n x.
Proof.
simple induction n.
intros.
elim (lt_n_O _ H).
intros.
simpl in |- *.
induction (le_lt_or_eq i n0).
eapply le_trans.
apply H.
assumption.
apply le_max_r.
rewrite H1.
apply le_max_l.
apply lt_n_Sm_le.
assumption.
