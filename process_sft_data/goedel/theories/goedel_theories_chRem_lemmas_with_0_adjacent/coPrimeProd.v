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

Lemma coPrimeProd : forall (n : nat) (x : nat -> nat), (forall z1 z2 : nat, z1 < S n -> z2 < S n -> z1 <> z2 -> CoPrime (x z1) (x z2)) -> (forall z : nat, z < S n -> x z > 0) -> CoPrime (prod n x) (x n).
Proof.
intro.
induction n as [| n Hrecn].
intros.
simpl in |- *.
apply coPrime1.
intros.
assert (forall z1 z2 : nat, z1 < S n -> z2 < S n -> z1 <> z2 -> CoPrime (x z1) (x z2)).
intros.
apply H.
apply lt_S.
assumption.
apply lt_S.
assumption.
assumption.
simpl in |- *.
apply coPrimeMult3.
apply H0.
apply lt_S.
apply lt_n_Sn.
apply prodBig1.
intros.
apply H0.
do 2 apply lt_S.
assumption.
apply H0.
apply lt_n_Sn.
apply H.
apply lt_S.
apply lt_n_Sn.
apply lt_n_Sn.
auto.
set (A1 := fun a : nat => match eq_nat_dec a n with | left _ => x (S n) | right _ => x a end) in *.
assert (CoPrime (prod n A1) (A1 n)).
apply Hrecn.
intros.
unfold A1 in |- *.
induction (eq_nat_dec z1 n).
induction (eq_nat_dec z2 n).
elim H4.
rewrite a0.
assumption.
apply H.
apply lt_n_Sn.
apply lt_S.
assumption.
unfold not in |- *; intros.
rewrite H5 in H3.
elim (lt_irrefl _ H3).
induction (eq_nat_dec z2 n).
apply H.
apply lt_S.
assumption.
apply lt_n_Sn.
unfold not in |- *; intros.
rewrite H5 in H2.
elim (lt_irrefl _ H2).
apply H.
apply lt_S.
assumption.
apply lt_S.
assumption.
assumption.
intros.
unfold A1 in |- *.
induction (eq_nat_dec z n).
apply H0.
apply lt_n_Sn.
apply H0.
apply lt_S.
assumption.
auto.
replace (x (S n)) with (A1 n).
replace (prod n x) with (prod n A1).
assumption.
apply sameProd.
intros.
unfold A1 in |- *.
induction (eq_nat_dec z n).
rewrite a in H3.
elim (lt_irrefl _ H3).
reflexivity.
unfold A1 in |- *.
induction (eq_nat_dec n n).
reflexivity.
elim b.
reflexivity.
