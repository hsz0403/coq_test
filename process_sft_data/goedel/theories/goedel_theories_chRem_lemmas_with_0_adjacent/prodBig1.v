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

Lemma prodBig1 : forall (n : nat) (x : nat -> nat), (forall z : nat, z < n -> x z > 0) -> prod n x > 0.
Proof.
intro.
induction n as [| n Hrecn].
intros.
simpl in |- *.
apply gt_Sn_n.
intros.
simpl in |- *.
apply multBig1.
apply H.
apply lt_n_Sn.
apply Hrecn.
intros.
apply H.
apply lt_S.
assumption.
