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

Lemma multO : forall a b : nat, a * b = 0 -> a = 0 \/ b = 0.
Proof.
intros.
induction (mult_O_le b a).
auto.
rewrite H in H0.
right.
symmetry in |- *.
apply le_n_O_eq.
Admitted.

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
Admitted.

Lemma coPrimeMult2 : forall a b c : nat, CoPrime a b -> Divides a c -> Divides b c -> Divides (a * b) c.
Proof.
intros.
induction H1 as (x, H1).
assert (Divides a x).
eapply coPrimeMult.
apply H.
rewrite <- H1.
assumption.
induction H2 as (x0, H2).
exists x0.
rewrite (mult_comm a).
rewrite (mult_assoc_reverse b).
rewrite <- H2.
Admitted.

Lemma ltgt1 : forall a b : nat, a < b -> b > 0.
Proof.
intros.
unfold gt in |- *.
eapply le_lt_trans.
apply le_O_n.
Admitted.

Lemma minus_le : forall a b : nat, a - b <= a.
Proof.
intros.
induction b as [| b Hrecb].
rewrite <- minus_n_O.
apply le_n.
induction (le_or_lt (S b) a).
apply lt_le_weak.
apply lt_minus.
assumption.
apply lt_O_Sn.
rewrite not_le_minus_0.
apply le_O_n.
apply lt_not_le.
Admitted.

Lemma minus1 : forall a b c : Z, (a - c)%Z = (b - c)%Z -> a = b.
Proof.
intros.
rewrite <- (Zminus_plus c b).
rewrite <- (Zminus_plus c a).
unfold Zminus in H.
unfold Zminus in |- *.
rewrite Zplus_assoc_reverse.
rewrite H.
rewrite Zplus_assoc_reverse.
Admitted.

Lemma chRem2 : forall b1 r1 b2 r2 q : Z, (0 <= r1)%Z -> (0 <= r2)%Z -> (r1 < q)%Z -> (r2 < q)%Z -> (b1 * q + r1)%Z = (b2 * q + r2)%Z -> r1 = r2.
Proof.
intros.
assert (((b1 - b2) * q)%Z = (r2 - r1)%Z).
rewrite Zmult_minus_distr_r.
apply Zplus_minus_eq.
unfold Zminus in |- *.
rewrite Zplus_assoc.
fold (r1 + b1 * q - b2 * q)%Z in |- *.
apply Zplus_minus_eq.
rewrite Zplus_comm.
assumption.
induction (Zle_or_lt 0 (b1 - b2)).
induction (Zle_lt_or_eq _ _ H5).
assert (1 <= b1 - b2)%Z.
replace 1%Z with (Z.succ 0).
apply Zlt_le_succ.
assumption.
auto.
assert (q <= r2 - r1)%Z.
replace q with (1 * q)%Z.
rewrite <- H4.
apply Zmult_le_compat_r.
assumption.
eapply Z.le_trans.
apply H.
apply Zlt_le_weak.
assumption.
apply Zmult_1_l.
set (A1 := Zplus_lt_le_compat r2 q (- r1) 0 H2) in *.
assert (r2 - r1 < q)%Z.
replace q with (q + 0)%Z.
unfold Zminus in |- *.
apply A1.
eapply (fun a b : Z => Zplus_le_reg_l a b r1).
rewrite Zplus_opp_r.
rewrite <- Zplus_0_r_reverse.
assumption.
rewrite <- Zplus_0_r_reverse.
reflexivity.
elim (Zle_not_lt q (r2 - r1)).
assumption.
assumption.
rewrite <- H6 in H4.
rewrite Zmult_comm in H4.
rewrite <- Zmult_0_r_reverse in H4.
rewrite <- (Zplus_opp_r r2) in H4.
unfold Zminus in H4.
apply Z.opp_inj.
symmetry in |- *.
eapply Zplus_reg_l.
apply H4.
assert (1 <= b2 - b1)%Z.
replace 1%Z with (Z.succ 0).
apply Zlt_le_succ.
apply (Zplus_lt_reg_l 0 (b2 - b1) b1).
rewrite Zplus_minus.
rewrite <- Zplus_0_r_reverse.
apply (Zplus_lt_reg_l b1 b2 (- b2)).
rewrite Zplus_opp_l.
rewrite Zplus_comm.
unfold Zminus in H5.
assumption.
auto.
assert (((b2 - b1) * q)%Z = (r1 - r2)%Z).
rewrite Zmult_minus_distr_r.
apply Zplus_minus_eq.
unfold Zminus in |- *.
rewrite Zplus_assoc.
fold (r2 + b2 * q - b1 * q)%Z in |- *.
apply Zplus_minus_eq.
rewrite Zplus_comm.
symmetry in |- *.
assumption.
assert (q <= r1 - r2)%Z.
replace q with (1 * q)%Z.
rewrite <- H7.
apply Zmult_le_compat_r.
assumption.
eapply Z.le_trans.
apply H.
apply Zlt_le_weak.
assumption.
apply Zmult_1_l.
set (A1 := Zplus_lt_le_compat r1 q (- r2) 0 H1) in *.
assert (r1 - r2 < q)%Z.
replace q with (q + 0)%Z.
unfold Zminus in |- *.
apply A1.
eapply (fun a b : Z => Zplus_le_reg_l a b r2).
rewrite Zplus_opp_r.
rewrite <- Zplus_0_r_reverse.
assumption.
rewrite <- Zplus_0_r_reverse.
reflexivity.
elim (Zle_not_lt q (r1 - r2)).
assumption.
Admitted.

Lemma chRem3 : forall a b : nat, Z_of_nat a = Z_of_nat b -> a = b.
Proof.
double induction a b.
reflexivity.
intros.
discriminate H0.
intros.
discriminate H0.
intros.
repeat rewrite Znat.inj_S in H1.
apply eq_S.
apply H0.
apply Z.succ_inj.
Admitted.

Lemma uniqueRem : forall r1 r2 b : nat, b > 0 -> forall a : nat, (exists q : nat, a = q * b + r1 /\ b > r1) -> (exists q : nat, a = q * b + r2 /\ b > r2) -> r1 = r2.
Proof.
intros.
induction H0 as (x, H0); induction H0 as (H0, H2).
induction H1 as (x0, H1); induction H1 as (H1, H3).
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
apply H2.
apply Znat.inj_lt.
apply H3.
repeat rewrite <- Znat.inj_mult.
repeat rewrite <- Znat.inj_plus.
apply Znat.inj_eq.
transitivity a.
symmetry in |- *.
apply H0.
Admitted.

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
Admitted.

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
Admitted.

Lemma coPrimeSym : forall a b : nat, CoPrime a b -> CoPrime b a.
Proof.
unfold CoPrime in |- *.
intros.
apply gcd_sym.
assumption.
