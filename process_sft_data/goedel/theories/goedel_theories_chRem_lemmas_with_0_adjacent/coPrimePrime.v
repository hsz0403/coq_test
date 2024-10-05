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

Lemma coPrimePrime : forall a b : nat, (forall p : nat, Prime p -> ~ Divides p a \/ ~ Divides p b) -> CoPrime a b.
Proof.
intros.
unfold CoPrime in |- *.
split.
split.
exists a.
rewrite mult_1_l.
apply abs_inj.
exists b.
rewrite mult_1_l.
apply abs_inj.
intros.
induction H0 as (H0, H1).
rewrite abs_inj in H0.
rewrite abs_inj in H1.
induction (le_or_lt e 1).
assumption.
induction (primeDiv _ H2).
induction H3 as (H3, H4).
induction (H _ H3).
elim H5.
eapply div_trans.
apply H4.
assumption.
elim H5.
eapply div_trans.
apply H4.
assumption.
