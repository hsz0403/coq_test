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

Theorem betaTheorem1 : forall (n : nat) (y : nat -> nat), {a : nat * nat | forall z : nat, z < n -> y z = snd (proj1_sig (modulo (coPrimeBeta z (snd a)) (gtBeta z (snd a)) (fst a)))}.
Proof.
intros.
set (c := factorial (max n (maxBeta n y))) in *.
set (x := fun z : nat => coPrimeBeta z c) in *.
assert (forall z1 z2 : nat, z1 < n -> z2 < n -> z1 <> z2 -> CoPrime (x z1) (x z2)).
intros.
unfold x in |- *.
eapply coPrimeSeq.
eapply div_trans.
unfold factorial in |- *.
apply divProd2.
apply le_max_l.
unfold c, factorial in |- *.
apply div_refl.
assumption.
apply lt_le_weak.
assumption.
apply lt_le_weak.
assumption.
assert (forall z : nat, z < n -> y z < x z).
intros.
unfold x, coPrimeBeta in |- *.
apply le_lt_n_Sm.
induction (mult_O_le c (S z)).
discriminate H1.
apply le_trans with c.
unfold c in |- *.
apply le_trans with (max n (maxBeta n y)).
apply le_trans with (maxBeta n y).
apply maxBetaLe.
assumption.
apply le_max_r.
generalize (max n (maxBeta n y)).
intros.
induction n0 as [| n0 Hrecn0].
simpl in |- *.
apply le_n_Sn.
induction n0 as [| n0 Hrecn1].
simpl in |- *.
apply le_n.
assert (factorial n0 > 0).
unfold factorial in |- *.
apply prodBig1.
intros.
apply gt_Sn_O.
simpl in |- *.
eapply le_trans with (1 + (1 + n0 * (factorial n0 + n0 * factorial n0))).
simpl in |- *.
repeat apply le_n_S.
induction (mult_O_le n0 (factorial n0 + n0 * factorial n0)).
unfold gt in H2.
assert (factorial n0 = factorial n0 + 0).
rewrite plus_comm.
auto.
assert (0 < factorial n0).
assumption.
rewrite H4 in H2.
set (A1 := factorial n0 + 0) in *.
rewrite <- H3 in H2.
unfold A1 in H2.
clear H4 A1.
assert (n0 * factorial n0 < 0).
eapply plus_lt_reg_l.
apply H2.
elim (lt_n_O _ H4).
rewrite mult_comm.
assumption.
apply plus_le_compat.
apply le_plus_trans.
apply lt_n_Sm_le.
apply lt_n_S.
assumption.
apply plus_le_compat.
apply le_plus_trans.
apply lt_n_Sm_le.
apply lt_n_S.
assumption.
apply le_n.
rewrite mult_comm.
assumption.
induction (chRem _ _ H _ H0).
exists (x0, c).
intros.
induction p as (H2, H3).
rewrite (H3 z H1).
induction (modulo (x z) (ltgt1 (y z) (x z) (H0 z H1)) x0).
replace (snd (x0, c)) with c.
replace (fst (x0, c)) with x0.
induction (modulo (coPrimeBeta z c) (gtBeta z c) x0).
simpl in |- *.
eapply uniqueRem.
apply gtBeta.
unfold x in p.
exists (fst x1).
apply p.
exists (fst x2).
apply p0.
auto.
auto.
