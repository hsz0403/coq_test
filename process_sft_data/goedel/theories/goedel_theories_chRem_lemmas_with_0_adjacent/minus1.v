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

Lemma minus1 : forall a b c : Z, (a - c)%Z = (b - c)%Z -> a = b.
Proof.
intros.
rewrite <- (Zminus_plus c b).
rewrite <- (Zminus_plus c a).
unfold Zminus in H.
unfold Zminus in |- *.
rewrite Zplus_assoc_reverse.
rewrite H.
rewrite Zplus_assoc_reverse.
reflexivity.
