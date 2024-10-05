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

Lemma sameProd : forall (n : nat) (x1 x2 : nat -> nat), (forall z : nat, z < n -> x1 z = x2 z) -> prod n x1 = prod n x2.
Proof.
intro n.
induction n as [| n Hrecn].
intros.
auto.
intros.
simpl in |- *.
replace (x1 n) with (x2 n).
replace (prod n x1) with (prod n x2).
reflexivity.
apply Hrecn.
intros.
symmetry in |- *.
apply H.
apply lt_S.
assumption.
symmetry in |- *.
apply H.
apply lt_n_Sn.
