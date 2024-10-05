Require Import Reals Omega mathcomp.ssreflect.ssreflect.
Require Import Rbar Rcomplements Continuity Derive Hierarchy RInt PSeries.
Require Import Lim_seq RInt_analysis.
Section nat_to_ring.
Context {K : Ring}.
Definition nat_to_ring (n : nat) : K := sum_n_m (fun _ => one) 1 n.
End nat_to_ring.
Section is_derive_mult.
Context {K : AbsRing}.
End is_derive_mult.

Lemma CV_radius_atan : CV_radius (fun n => (-1)^n / (INR (S (n + n)))) = 1.
Proof.
apply eq_trans with (2 := f_equal Finite Rinv_1).
apply CV_radius_finite_DAlembert.
intros n.
apply Rmult_integral_contrapositive_currified.
apply pow_nonzero.
apply Rlt_not_eq, Rminus_lt_0 ; ring_simplify ; apply Rlt_0_1.
rewrite S_INR ; by apply Rgt_not_eq, RinvN_pos.
by apply Rlt_0_1.
apply is_lim_seq_ext with (fun n => 1 - 2 / (2 * INR n + 3)).
intros n.
rewrite -plus_n_Sm plus_Sn_m !S_INR plus_INR.
assert (0 < INR n + INR n + 1).
rewrite -plus_INR -S_INR.
by apply (lt_INR O), lt_O_Sn.
assert (0 < INR n + INR n + 1 + 1 + 1).
rewrite -plus_INR -!S_INR.
by apply (lt_INR O), lt_O_Sn.
rewrite !Rabs_div ; try by apply Rgt_not_eq.
rewrite -!RPow_abs Rabs_m1 !pow1 !Rabs_pos_eq ; try by left.
field.
split ; by apply Rgt_not_eq.
apply Rmult_integral_contrapositive_currified.
apply pow_nonzero.
apply Rlt_not_eq, Rminus_lt_0 ; ring_simplify ; apply Rlt_0_1.
rewrite -plus_INR ; by apply Rgt_not_eq, RinvN_pos.
evar_last.
apply is_lim_seq_minus'.
apply filterlim_const.
eapply is_lim_seq_div.
apply is_lim_seq_const.
eapply is_lim_seq_plus.
eapply is_lim_seq_mult.
apply is_lim_seq_const.
apply is_lim_seq_INR.
apply is_Rbar_mult_sym, is_Rbar_mult_p_infty_pos.
by apply Rlt_0_2.
apply is_lim_seq_const.
reflexivity ; simpl.
by [].
reflexivity.
simpl ; apply f_equal ; ring.
