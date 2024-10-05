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

Lemma coPrimeMult2 : forall a b c : nat, CoPrime a b -> Divides a c -> Divides b c -> Divides (a * b) c.
Proof.
intros.
induction H1 as (x, H1).
assert (Divides a x).
eapply coPrimeMult.
apply H.
rewrite <- H1.
assumption.
induction H2 as (x0, H2).
exists x0.
rewrite (mult_comm a).
rewrite (mult_assoc_reverse b).
rewrite <- H2.
assumption.
