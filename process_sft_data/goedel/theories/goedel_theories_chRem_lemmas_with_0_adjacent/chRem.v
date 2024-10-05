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

Lemma chRem : forall (n : nat) (x : nat -> nat), (forall z1 z2 : nat, z1 < n -> z2 < n -> z1 <> z2 -> CoPrime (x z1) (x z2)) -> forall (y : nat -> nat) (py : forall z : nat, z < n -> y z < x z), {a : nat | a < prod n x /\ (forall (z : nat) (pz : z < n), y z = snd (proj1_sig (modulo (x z) (ltgt1 _ _ (py z pz)) a)))}.
Proof.
intro.
induction n as [| n Hrecn].
intros.
exists 0.
split.
simpl in |- *.
apply lt_O_Sn.
intros.
elim (lt_n_O _ pz).
intros.
assert (forall z1 z2 : nat, z1 < n -> z2 < n -> z1 <> z2 -> CoPrime (x z1) (x z2)).
intros.
apply H.
apply lt_S.
assumption.
apply lt_S.
assumption.
assumption.
assert (forall z : nat, z < n -> y z < x z).
intros.
apply py.
apply lt_S.
assumption.
induction (Hrecn x H0 y H1).
clear Hrecn.
induction p as (H2, H3).
assert (CoPrime (prod n x) (x n)).
apply coPrimeProd.
apply H.
intros.
eapply ltgt1.
apply py.
assumption.
assert (y n < x n).
apply py.
apply lt_n_Sn.
induction (chineseRemainderTheorem (prod n x) (x n) H4 x0 (y n) H2 H5).
exists x1.
induction p as (H6, H7).
induction H7 as (H7, H8).
split.
simpl in |- *.
rewrite mult_comm.
assumption.
intros.
induction (le_lt_or_eq z n).
assert (y z = snd (proj1_sig (modulo (x z) (ltgt1 (y z) (x z) (H1 z H9)) x0))).
apply H3.
induction (modulo (x z) (ltgt1 (y z) (x z) (H1 z H9)) x0).
simpl in H10.
induction (modulo (x z) (ltgt1 (y z) (x z) (py z pz)) x1).
simpl in |- *.
rewrite H10.
induction (modulo (prod n x) (ltgt1 x0 (prod n x) H2) x1).
simpl in H7.
rewrite H7 in p.
induction p1 as (H11, H12).
induction p as (H13, H14).
induction p0 as (H15, H16).
rewrite H13 in H11.
apply uniqueRem with (x z) x1.
apply (ltgt1 (y z) (x z) (py z pz)).
assert (Divides (x z) (prod n x)).
apply divProd.
assumption.
induction H17 as (x5, H17).
rewrite H17 in H11.
rewrite (mult_comm (x z)) in H11.
rewrite mult_assoc in H11.
rewrite plus_assoc in H11.
rewrite <- mult_plus_distr_r in H11.
exists (fst x4 * x5 + fst x2).
split.
apply H11.
assumption.
exists (fst x3).
auto.
induction (modulo (x z) (ltgt1 (y z) (x z) (py z pz)) x1).
induction (modulo (x n) (ltgt1 (y n) (x n) H5) x1).
simpl in H8.
simpl in |- *.
rewrite H9.
rewrite H8.
eapply uniqueRem.
apply (ltgt1 (y n) (x n) H5).
exists (fst x3).
apply p0.
exists (fst x2).
rewrite H9 in p.
assumption.
apply lt_n_Sm_le.
assumption.
