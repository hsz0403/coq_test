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

Lemma chRem1 : forall b : nat, b > 0 -> forall a : Z, {p : Z * nat | snd p < b /\ Z_of_nat (snd p) = (fst p * Z_of_nat b + a)%Z}.
Proof.
intros.
assert (forall a' : Z, (a' >= 0)%Z -> {p : Z * nat | snd p < b /\ Z_of_nat (snd p) = (fst p * Z_of_nat b + a')%Z}).
intros.
set (A := Z.abs_nat a') in *.
induction (modulo b H A).
induction x as (a0, b0).
exists ((- Z_of_nat a0)%Z, b0).
induction p as (H1, H2).
split.
apply H2.
rewrite <- (inj_abs_pos a').
replace (fst ((- Z_of_nat a0)%Z, b0)) with (- Z_of_nat a0)%Z.
replace (snd ((- Z_of_nat a0)%Z, b0)) with b0.
rewrite Zopp_mult_distr_l_reverse.
rewrite Zplus_comm.
fold (Z_of_nat (Z.abs_nat a') - Z_of_nat a0 * Z_of_nat b)%Z in |- *.
apply Zplus_minus_eq.
rewrite <- Znat.inj_mult.
rewrite <- Znat.inj_plus.
apply Znat.inj_eq.
apply H1.
auto.
auto.
assumption.
induction (Z_ge_lt_dec a 0).
apply H0.
assumption.
assert (a + Z_of_nat b * - a >= 0)%Z.
induction b as [| b Hrecb].
elim (lt_irrefl _ H).
rewrite Znat.inj_S.
rewrite Zmult_comm.
rewrite <- Zmult_succ_r_reverse.
fold (- a * Z_of_nat b - a)%Z in |- *.
rewrite Zplus_minus.
replace 0%Z with (0 * Z_of_nat b)%Z.
apply Zmult_ge_compat_r.
rewrite (Zminus_diag_reverse a).
rewrite <- (Zplus_0_l (- a)).
unfold Zminus in |- *.
apply Z.le_ge.
apply Zplus_le_compat_r.
apply Zlt_le_weak.
assumption.
replace 0%Z with (Z_of_nat 0).
apply Znat.inj_ge.
unfold ge in |- *.
apply le_O_n.
auto.
auto.
induction (H0 _ H1).
induction p as (H2, H3).
induction x as (a0, b1).
exists ((a0 - a)%Z, b1).
split.
simpl in |- *.
apply H2.
cbv beta iota zeta delta [fst snd] in |- *.
cbv beta iota zeta delta [fst snd] in H3.
rewrite H3.
rewrite (Zplus_comm a).
rewrite Zplus_assoc.
apply Zplus_eq_compat.
rewrite Zmult_minus_distr_r.
unfold Zminus in |- *.
apply Zplus_eq_compat.
reflexivity.
rewrite Zmult_comm.
apply Zopp_mult_distr_l_reverse.
reflexivity.
