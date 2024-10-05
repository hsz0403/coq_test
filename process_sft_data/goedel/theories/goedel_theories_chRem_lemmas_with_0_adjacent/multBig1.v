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

Lemma multBig1 : forall a b : nat, a > 0 -> b > 0 -> a * b > 0.
Proof.
intros.
induction a as [| a Hreca].
unfold gt in H.
elim (lt_n_O _ H).
unfold gt in |- *.
apply lt_le_trans with (b * 1).
rewrite mult_1_r.
apply H0.
rewrite (mult_comm (S a)).
apply (fun m n p : nat => mult_le_compat_l p n m).
apply le_n_S.
apply le_O_n.
