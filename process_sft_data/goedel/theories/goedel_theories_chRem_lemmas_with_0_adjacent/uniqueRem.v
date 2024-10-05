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

Lemma uniqueRem : forall r1 r2 b : nat, b > 0 -> forall a : nat, (exists q : nat, a = q * b + r1 /\ b > r1) -> (exists q : nat, a = q * b + r2 /\ b > r2) -> r1 = r2.
Proof.
intros.
induction H0 as (x, H0); induction H0 as (H0, H2).
induction H1 as (x0, H1); induction H1 as (H1, H3).
apply chRem3.
eapply chRem2.
replace 0%Z with (Z_of_nat 0).
apply Znat.inj_le.
apply le_O_n.
auto.
replace 0%Z with (Z_of_nat 0).
apply Znat.inj_le.
apply le_O_n.
auto.
apply Znat.inj_lt.
apply H2.
apply Znat.inj_lt.
apply H3.
repeat rewrite <- Znat.inj_mult.
repeat rewrite <- Znat.inj_plus.
apply Znat.inj_eq.
transitivity a.
symmetry in |- *.
apply H0.
apply H1.
