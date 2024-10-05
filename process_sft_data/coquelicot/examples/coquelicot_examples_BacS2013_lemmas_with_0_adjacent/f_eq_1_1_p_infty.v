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

Lemma f_eq_1_1_p_infty : exists x, 1 <= x /\ f x = 1.
Proof.
case: (IVT_Rbar_incr (fun x => - f x) 1 p_infty (-2) 0 (-1)).
replace (-2) with (-f 1).
apply (is_lim_continuity (fun x => - f x)).
apply continuity_pt_opp.
apply derivable_continuous_pt.
exists (((2 - 2) - 2 * ln 1) / 1 ^ 2) ; apply is_derive_Reals, Dfab.
by apply Rlt_0_1.
rewrite /f /fab ln_1 /= ; field.
evar_last.
apply is_lim_opp.
by apply Lim_f_p_infty.
simpl ; by rewrite Ropp_0.
move => x H0x Hx1.
apply continuity_pt_opp.
apply derivable_continuous_pt.
exists (((2 - 2) - 2 * ln x) / x ^ 2) ; apply is_derive_Reals, Dfab.
by apply Rlt_trans with (1 := Rlt_0_1).
by [].
split ; apply Rminus_lt_0 ; ring_simplify ; by apply Rlt_0_1.
move => x [H0x [Hx1 Hfx]].
exists x ; split.
by apply Rlt_le.
rewrite -(Ropp_involutive (f x)) Hfx ; ring.
