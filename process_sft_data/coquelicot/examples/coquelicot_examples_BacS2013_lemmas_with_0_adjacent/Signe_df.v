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

Lemma Signe_df : forall x, 0 < x -> sign (Derive f x) = sign (- ln x).
Proof.
move => x Hx.
rewrite (is_derive_unique f x _ (Dfab 2 2 x Hx)).
replace ((2 - 2 - 2 * ln x) / x ^ 2) with (2 / x ^ 2 * (- ln x)) by (field ; now apply Rgt_not_eq).
rewrite sign_mult sign_eq_1.
apply Rmult_1_l.
apply Rdiv_lt_0_compat.
apply Rlt_0_2.
apply pow2_gt_0.
by apply Rgt_not_eq.
