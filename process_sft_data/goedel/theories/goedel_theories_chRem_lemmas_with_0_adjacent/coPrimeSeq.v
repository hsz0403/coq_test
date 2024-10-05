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

Lemma coPrimeSeq : forall c i j n : nat, Divides (factorial n) c -> i <> j -> i <= n -> j <= n -> CoPrime (coPrimeBeta i c) (coPrimeBeta j c).
Proof.
unfold coPrimeBeta in |- *.
intros.
induction (nat_total_order _ _ H0).
eapply coPrimeSeqHelp.
apply H.
assumption.
assumption.
assumption.
apply coPrimeSym.
eapply coPrimeSeqHelp.
apply H.
assumption.
assumption.
assumption.
