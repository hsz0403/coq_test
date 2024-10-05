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

Lemma chineseRemainderTheoremHelp : forall x1 x2 : nat, CoPrime x1 x2 -> forall (a b : nat) (pa : a < x1) (pb : b < x2), a <= b -> {y : nat | y < x1 * x2 /\ a = snd (proj1_sig (modulo x1 (ltgt1 _ _ pa) y)) /\ b = snd (proj1_sig (modulo x2 (ltgt1 _ _ pb) y))}.
Proof.
intros.
unfold CoPrime in H.
induction (gcd_lincomb_nat_dec _ _ _ (ltgt1 _ _ pa) H).
induction x as (a0, b0).
set (A := Z_of_nat a) in *.
set (B := Z_of_nat b) in *.
set (X1 := Z_of_nat x1) in *.
set (X2 := Z_of_nat x2) in *.
set (y := (a0 * (B - A))%Z) in *.
set (z := (b0 * (A - B))%Z) in *.
set (d := (A + X1 * y)%Z) in *.
assert (d = (B + X2 * z)%Z).
unfold d in |- *.
simpl in p.
apply minus1 with (X2 * z)%Z.
rewrite (Zplus_comm B).
rewrite Zminus_plus.
unfold z in |- *.
replace (A - B)%Z with (- (B - A))%Z.
unfold Zminus in |- *.
rewrite (Zmult_comm b0).
rewrite Zopp_mult_distr_l_reverse.
rewrite (Zmult_comm X2).
rewrite Zopp_mult_distr_l_reverse.
rewrite Z.opp_involutive.
unfold y in |- *.
rewrite (Zmult_assoc_reverse (B + - A)).
rewrite (Zmult_comm (B + - A)).
rewrite (Zmult_assoc X1).
rewrite (Zmult_comm b0).
rewrite Zplus_assoc_reverse.
rewrite <- Zmult_plus_distr_l.
rewrite <- p.
rewrite Zmult_1_l.
fold (B - A)%Z in |- *.
apply Zplus_minus.
unfold Zminus in |- *.
rewrite Zopp_plus_distr.
rewrite Zplus_comm.
rewrite Z.opp_involutive.
reflexivity.
assert (x1 * x2 > 0).
replace 0 with (0 * x2).
unfold gt in |- *.
rewrite mult_comm.
rewrite (mult_comm x1).
induction x2 as [| x2 Hrecx2].
elim (lt_n_O _ pb).
apply mult_S_lt_compat_l.
fold (x1 > 0) in |- *.
eapply ltgt1.
apply pa.
auto.
induction (chRem1 _ H2 d).
induction p0 as (H3, H4).
induction x as (a1, b1).
exists b1.
split.
apply H3.
cbv beta iota zeta delta [snd fst] in H4.
cbv beta iota zeta delta [snd fst] in p.
split.
induction (modulo x1 (ltgt1 a x1 pa) b1).
induction x as (a2, b2).
simpl in |- *.
induction p0 as (H5, H6).
cbv beta iota zeta delta [snd fst] in H5.
rewrite H5 in H4.
unfold d in H4.
unfold A, X1 in H4.
apply chRem3.
eapply chRem2.
replace 0%Z with (Z_of_nat 0).
apply Znat.inj_le.
apply le_O_n.
auto.
replace 0%Z with (Z_of_nat 0).
apply Znat.inj_le.
apply le_O_n.
auto.
apply Znat.inj_lt.
apply pa.
apply Znat.inj_lt.
apply H6.
rewrite Znat.inj_plus in H4.
repeat rewrite Znat.inj_mult in H4.
symmetry in |- *.
rewrite (Zplus_comm (Z_of_nat a)) in H4.
rewrite Zplus_assoc in H4.
rewrite Zmult_assoc in H4.
rewrite (Zmult_comm a1) in H4.
rewrite (Zmult_assoc_reverse (Z_of_nat x1)) in H4.
rewrite <- Zmult_plus_distr_r in H4.
rewrite (Zmult_comm (Z_of_nat x1)) in H4.
apply H4.
induction (modulo x2 (ltgt1 b x2 pb) b1).
simpl in |- *.
induction x as (a2, b2).
cbv beta iota zeta delta [snd fst] in p0.
induction p0 as (H5, H6).
rewrite H5 in H4.
rewrite H1 in H4.
unfold B, X2 in H4.
apply chRem3.
eapply chRem2.
replace 0%Z with (Z_of_nat 0).
apply Znat.inj_le.
apply le_O_n.
auto.
replace 0%Z with (Z_of_nat 0).
apply Znat.inj_le.
apply le_O_n.
auto.
apply Znat.inj_lt.
apply pb.
apply Znat.inj_lt.
apply H6.
rewrite Znat.inj_plus in H4.
repeat rewrite Znat.inj_mult in H4.
symmetry in |- *.
rewrite (Zplus_comm (Z_of_nat b)) in H4.
rewrite Zmult_assoc in H4.
rewrite Zplus_assoc in H4.
rewrite (Zmult_comm a1) in H4.
rewrite (Zmult_comm (Z_of_nat x2)) in H4.
rewrite <- Zmult_plus_distr_l in H4.
apply H4.
