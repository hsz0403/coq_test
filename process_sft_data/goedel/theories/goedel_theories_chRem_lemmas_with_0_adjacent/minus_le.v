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

Lemma minus_le : forall a b : nat, a - b <= a.
Proof.
intros.
induction b as [| b Hrecb].
rewrite <- minus_n_O.
apply le_n.
induction (le_or_lt (S b) a).
apply lt_le_weak.
apply lt_minus.
assumption.
apply lt_O_Sn.
rewrite not_le_minus_0.
apply le_O_n.
apply lt_not_le.
assumption.
