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

Lemma gcd_lincomb_nat_dec : forall x y d : nat, x > 0 -> gcd (Z_of_nat x) (Z_of_nat y) d -> {a : Z * Z | Z_of_nat d = (Z_of_nat x * fst a + Z_of_nat y * snd a)%Z}.
Proof.
unfold LinComb in |- *.
intro x.
apply (lt_wf_rec x).
intros X IH.
intros.
elim (modulo X H y).
intro z.
elim z.
intros q r.
clear z.
simpl in |- *.
case r.
intros.
induction p as (H1, H2).
rewrite <- plus_n_O in H1.
exists (1%Z, 0%Z).
replace (fst (1%Z, 0%Z)) with 1%Z.
replace (snd (1%Z, 0%Z)) with 0%Z.
rewrite <- Zmult_0_r_reverse.
rewrite <- Zplus_0_r_reverse.
rewrite Zmult_comm.
rewrite Zmult_1_l.
apply Znat.inj_eq.
apply (euclid_gcd d X (Z_of_nat y) (Z_of_nat X) (Z_of_nat q) 0).
rewrite <- Zplus_0_r_reverse.
rewrite <- Znat.inj_mult.
apply Znat.inj_eq.
assumption.
apply gcd_sym.
assumption.
apply gcd_0_l.
assumption.
auto.
auto.
intro r1.
intros.
induction p as (H1, H2).
elim (IH (S r1) H2 X d).
intro z.
elim z.
intros delta gamma.
clear z.
replace (fst (delta, gamma)) with delta.
replace (snd (delta, gamma)) with gamma.
intros.
exists ((gamma - Z_of_nat q * delta)%Z, delta).
replace (fst ((gamma - Z_of_nat q * delta)%Z, delta)) with (gamma - Z_of_nat q * delta)%Z.
replace (snd ((gamma - Z_of_nat q * delta)%Z, delta)) with delta.
rewrite p.
rewrite H1.
unfold Zminus in |- *.
rewrite Zmult_plus_distr_r.
rewrite Znat.inj_plus.
rewrite Zmult_plus_distr_l.
rewrite Znat.inj_mult.
rewrite <- Zopp_mult_distr_l_reverse.
rewrite (Zmult_assoc (Z_of_nat X)).
rewrite (Zmult_comm (Z_of_nat X) (- Z_of_nat q)).
rewrite Zopp_mult_distr_l_reverse.
rewrite Zopp_mult_distr_l_reverse.
rewrite (Zplus_assoc_reverse (Z_of_nat X * gamma)).
rewrite <- Znat.inj_mult.
rewrite (Zplus_assoc (- (Z_of_nat (q * X) * delta))).
rewrite Zplus_opp_l.
simpl in |- *.
apply Zplus_comm.
auto.
auto.
auto.
auto.
apply gt_Sn_O.
apply (euclid_gcd1 d (Z_of_nat y) (Z_of_nat X) (Z_of_nat q) (Z_of_nat (S r1))).
apply gcd_sym.
assumption.
rewrite <- Znat.inj_mult.
rewrite <- Znat.inj_plus.
apply Znat.inj_eq.
assumption.
