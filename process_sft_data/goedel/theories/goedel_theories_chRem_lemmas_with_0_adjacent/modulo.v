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

Lemma modulo : forall b : nat, b > 0 -> forall a : nat, {p : nat * nat | a = fst p * b + snd p /\ b > snd p}.
Proof.
intros.
apply (gt_wf_rec a).
intros.
induction (le_lt_dec b n).
assert (n > n - b).
unfold gt in |- *.
apply lt_minus.
assumption.
assumption.
induction (H0 _ H1).
induction x as (a1, b0).
simpl in p.
exists (S a1, b0).
simpl in |- *.
induction p as (H2, H3).
split.
rewrite plus_assoc_reverse.
rewrite <- H2.
apply le_plus_minus.
assumption.
assumption.
exists (0, n).
simpl in |- *.
split.
reflexivity.
assumption.
