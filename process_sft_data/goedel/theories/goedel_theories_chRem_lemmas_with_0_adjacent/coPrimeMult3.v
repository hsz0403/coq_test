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

Lemma coPrimeMult3 : forall a b c : nat, a > 0 -> b > 0 -> c > 0 -> CoPrime a c -> CoPrime b c -> CoPrime (a * b) c.
Proof.
intros.
assert (LinComb (Z_of_nat 1) (Z_of_nat a) (Z_of_nat c)).
apply gcd_lincomb_nat.
assumption.
apply H2.
assert (LinComb (Z_of_nat 1) (Z_of_nat b) (Z_of_nat c)).
apply gcd_lincomb_nat.
assumption.
apply H3.
induction H4 as (x, H4).
induction H4 as (x0, H4).
induction H5 as (x1, H5).
induction H5 as (x2, H5).
split.
split.
exists (Z.abs_nat (Z_of_nat (a * b))).
rewrite mult_1_l.
reflexivity.
exists (Z.abs_nat (Z_of_nat c)).
rewrite mult_1_l.
reflexivity.
intros.
induction H6 as (H6, H7).
set (A := Z_of_nat a) in *.
set (B := Z_of_nat b) in *.
set (C := Z_of_nat c) in *.
assert (1%Z = (A * B * (x * x1) + C * (x0 * B * x1 + x2 * A * x + x0 * x2 * C))%Z).
replace 1%Z with (Z_of_nat 1 * Z_of_nat 1)%Z.
rewrite (Zmult_comm C).
rewrite Zmult_plus_distr_l.
rewrite Zmult_plus_distr_l.
rewrite (Zplus_comm (x0 * B * x1 * C)).
rewrite Zmult_assoc_reverse.
rewrite (Zmult_assoc B).
rewrite (Zmult_comm B).
rewrite (Zmult_assoc_reverse x).
rewrite (Zmult_assoc A).
rewrite (Zmult_assoc_reverse x2).
rewrite (Zmult_comm x2).
rewrite (Zmult_assoc_reverse (A * x) x2).
repeat rewrite Zplus_assoc.
rewrite <- Zmult_plus_distr_r.
rewrite (Zmult_comm (x0 * B * x1)).
repeat rewrite (Zmult_assoc C).
rewrite (Zmult_assoc_reverse (C * x0)).
rewrite (Zmult_comm (x0 * x2)).
repeat rewrite (Zmult_assoc C).
rewrite (Zmult_assoc_reverse (C * x0)).
rewrite Zplus_assoc_reverse.
rewrite <- Zmult_plus_distr_r.
rewrite <- Zmult_plus_distr_l.
rewrite <- H4.
rewrite (Zmult_comm x2).
rewrite <- H5.
reflexivity.
auto.
assert (Divides e 1).
replace 1 with (Z.abs_nat 1).
replace e with (Z.abs_nat (Z_of_nat e)).
apply zdivdiv.
rewrite H8.
apply zdiv_plus_compat.
apply zdiv_mult_compat_l.
apply divzdiv.
unfold A, B in |- *.
rewrite <- Znat.inj_mult.
rewrite abs_inj.
assumption.
apply zdiv_mult_compat_l.
apply divzdiv.
rewrite abs_inj.
assumption.
apply abs_inj.
auto.
apply div_le.
apply lt_n_Sn.
assumption.
