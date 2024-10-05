Require Import Reals mathcomp.ssreflect.ssreflect.
Require Import Psatz.
Require Import Rcomplements Rbar Hierarchy.
Require Import Derive RInt Continuity Lim_seq ElemFct RInt_analysis.
Ltac pos_rat := repeat ( apply Rdiv_lt_0_compat || apply Rplus_lt_0_compat || apply Rmult_lt_0_compat) ; try by apply Rlt_0_1.
Definition fab (a b x : R) : R := (a + b * ln x) / x.
Definition f (x : R) : R := fab 2 2 x.
Fixpoint u (n : nat) : R := match n with | O => 2 | S n => 2/3 * u n + 1/3 * (INR n) + 1 end.
Definition v (n : nat) : R := u n - INR n.
Definition Su (n : nat) : R := sum_f_R0 u n.
Definition Tu (n : nat) : R := Su n / (INR n) ^ 2.

Lemma Q2a : forall n, u n <= INR n + 3.
Proof.
elim => [ | n IH] ; rewrite ?S_INR /=.
apply Rminus_le_0 ; ring_simplify ; apply Rle_0_1.
eapply Rle_trans.
apply Rplus_le_compat_r.
apply Rplus_le_compat_r.
apply Rmult_le_compat_l.
lra.
by apply IH.
lra.
