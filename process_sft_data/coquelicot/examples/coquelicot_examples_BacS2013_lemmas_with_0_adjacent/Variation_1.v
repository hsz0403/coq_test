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

Lemma Variation_1 : forall x y, 0 < x -> x < y -> y < 1 -> f x < f y.
Proof.
apply (incr_function _ 0 1 (fun x => (2 - 2 - 2 * ln x) / x ^ 2)).
move => x H0x Hx1.
by apply (Dfab 2 2 x).
move => x H0x Hx1.
apply sign_0_lt.
rewrite -(is_derive_unique _ _ _ (Dfab 2 2 x H0x)).
rewrite Signe_df.
apply -> sign_0_lt.
apply Ropp_lt_cancel ; rewrite Ropp_0 Ropp_involutive.
rewrite -ln_1.
by apply ln_increasing.
by apply H0x.
