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

Lemma primeDiv : forall a : nat, 1 < a -> exists p : nat, Prime p /\ Divides p a.
intro a.
apply (lt_wf_ind a).
clear a.
intros.
induction (primedec n).
exists n.
split.
assumption.
exists 1.
symmetry in |- *.
apply mult_1_r.
induction (nonprime_witness _ H0 H1).
induction H2 as (H2, H3).
induction H3 as (H3, H4).
induction (H _ H3 H2).
exists x0.
induction H5 as (H5, H6).
split.
assumption.
eapply div_trans.
apply H6.
assumption.
