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

Lemma Variation_2 : forall x y, 1 < x -> x < y -> f x > f y.
Proof.
move => x y H1x Hxy.
apply Ropp_lt_cancel.
apply (incr_function (fun x => - f x) 1 p_infty (fun z => - ((2 - 2 - 2 * ln z) / z ^ 2))).
move => z H1z _.
apply: is_derive_opp.
apply (Dfab 2 2 z).
by apply Rlt_trans with (1 := Rlt_0_1).
move => z H1z _.
apply Ropp_lt_cancel ; rewrite Ropp_0 Ropp_involutive.
apply sign_lt_0.
rewrite -(is_derive_unique _ _ _ (Dfab 2 2 z (Rlt_trans _ _ _ Rlt_0_1 H1z))).
rewrite Signe_df.
apply -> sign_lt_0.
apply Ropp_lt_cancel ; rewrite Ropp_0 Ropp_involutive.
rewrite -ln_1.
apply ln_increasing.
by apply Rlt_0_1.
by apply H1z.
by apply Rlt_trans with (1 := Rlt_0_1).
by [].
by [].
by [].
