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

Lemma is_lim_exp_p : is_lim (fun y => exp y) p_infty p_infty.
Proof.
apply is_lim_le_p_loc with (fun y => 1 + y).
exists 0 => y Hy.
by apply Rlt_le, exp_ineq1.
pattern p_infty at 2.
replace p_infty with (Rbar_plus 1 p_infty) by auto.
eapply is_lim_plus.
apply is_lim_const.
apply is_lim_id.
by [].
