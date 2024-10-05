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

Lemma RInt_f : is_RInt f ( / exp 1) 1 1.
Proof.
have Haux1: (0 < /exp 1).
apply Rinv_0_lt_compat.
apply exp_pos.
evar_last.
apply: is_RInt_derive.
move => x Hx.
apply If.
apply Rlt_le_trans with (2 := proj1 Hx).
apply Rmin_case.
by apply Haux1.
by apply Rlt_0_1.
move => x Hx.
apply continuity_pt_filterlim.
apply derivable_continuous_pt.
exists (((2 - 2) - 2 * ln x) / x ^ 2) ; apply is_derive_Reals, Dfab.
apply Rlt_le_trans with (2 := proj1 Hx).
apply Rmin_case.
by apply Haux1.
by apply Rlt_0_1.
rewrite /minus /= /plus /opp /= -[eq]/(@eq R).
rewrite ln_Rinv.
rewrite ln_exp.
rewrite ln_1.
ring.
by apply exp_pos.
