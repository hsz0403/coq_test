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

Lemma coPrimeMult : forall a b c : nat, CoPrime a b -> Divides a (b * c) -> Divides a c.
Proof.
intros.
unfold CoPrime in H.
induction a as [| a Hreca].
induction H0 as (x, H0).
induction (multO _ _ H0).
rewrite H1 in H.
unfold gcd in H.
induction H as (H, H2).
assert (2 <= 1).
apply H2.
split.
simpl in |- *.
exists 0.
rewrite mult_comm.
simpl in |- *.
reflexivity.
exists 0.
rewrite mult_comm.
simpl in |- *.
reflexivity.
elim (le_Sn_n _ H3).
exists 0.
rewrite H1.
auto.
clear Hreca.
assert (S a > 0).
apply gt_Sn_O.
induction (gcd_lincomb_nat _ _ _ H1 H).
induction H2 as (x0, H2).
induction H0 as (x1, H0).
assert ((1 * Z_of_nat c)%Z = (Z_of_nat (S a) * (x * Z_of_nat c + Z_of_nat x1 * x0))%Z).
rewrite (Zmult_comm (Z_of_nat (S a))).
rewrite Zmult_plus_distr_l.
rewrite (Zmult_comm (x * Z_of_nat c)).
rewrite (Zmult_comm (Z_of_nat x1 * x0)).
repeat rewrite Zmult_assoc.
rewrite <- Znat.inj_mult.
rewrite <- H0.
rewrite Znat.inj_mult.
rewrite (Zmult_comm (Z_of_nat b)).
rewrite (Zmult_assoc_reverse (Z_of_nat c)).
rewrite (Zmult_comm (Z_of_nat c)).
rewrite <- Zmult_plus_distr_l.
rewrite <- H2.
reflexivity.
rewrite Zmult_1_l in H3.
assert (ZDivides (Z_of_nat (S a)) (Z_of_nat c)).
unfold ZDivides in |- *.
exists (x * Z_of_nat c + Z_of_nat x1 * x0)%Z.
assumption.
clear H2 H3 x x0.
rewrite <- (abs_inj (S a)).
rewrite <- (abs_inj c).
apply zdivdiv.
assumption.
