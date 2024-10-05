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

Lemma filterlim_f_0 : filterlim f (at_right 0) (Rbar_locally m_infty).
Proof.
unfold f, fab.
eapply (filterlim_comp_2 _ _ Rmult).
eapply filterlim_comp_2.
apply filterlim_const.
eapply filterlim_comp_2.
apply filterlim_const.
by apply is_lim_ln_0.
apply (filterlim_Rbar_mult 2 m_infty m_infty).
unfold is_Rbar_mult, Rbar_mult'.
case: Rle_dec (Rlt_le _ _ Rlt_0_2) => // H _ ; case: Rle_lt_or_eq_dec (Rlt_not_eq _ _ Rlt_0_2) => //.
apply (filterlim_Rbar_plus 2 _ m_infty).
by [].
by apply filterlim_Rinv_0_right.
by apply (filterlim_Rbar_mult m_infty p_infty).
