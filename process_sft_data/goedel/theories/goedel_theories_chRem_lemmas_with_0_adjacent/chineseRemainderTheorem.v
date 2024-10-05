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

Lemma chineseRemainderTheorem : forall x1 x2 : nat, CoPrime x1 x2 -> forall (a b : nat) (pa : a < x1) (pb : b < x2), {y : nat | y < x1 * x2 /\ a = snd (proj1_sig (modulo x1 (ltgt1 _ _ pa) y)) /\ b = snd (proj1_sig (modulo x2 (ltgt1 _ _ pb) y))}.
Proof.
intros.
induction (le_lt_dec a b).
apply chineseRemainderTheoremHelp.
assumption.
assumption.
assert (b <= a).
apply lt_le_weak.
assumption.
assert (CoPrime x2 x1).
apply coPrimeSym.
assumption.
induction (chineseRemainderTheoremHelp _ _ H1 b a pb pa H0).
induction p as (H2, H3).
induction H3 as (H3, H4).
exists x.
split.
rewrite mult_comm.
assumption.
split.
assumption.
assumption.
