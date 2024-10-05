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
assumption.
