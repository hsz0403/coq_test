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

Theorem divProd2 : forall (n : nat) (x : nat -> nat) (i : nat), i <= n -> Divides (prod i x) (prod n x).
Proof.
simple induction n.
intros.
assert (0 = i).
apply le_n_O_eq.
assumption.
rewrite H0.
apply div_refl.
intros.
induction (le_lt_or_eq i (S n0)).
simpl in |- *.
rewrite mult_comm.
apply div_mult_compat_l.
apply H.
apply lt_n_Sm_le.
assumption.
rewrite H1.
apply div_refl.
assumption.
