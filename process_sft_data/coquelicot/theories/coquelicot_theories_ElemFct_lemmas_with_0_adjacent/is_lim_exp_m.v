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

Lemma is_lim_exp_m : is_lim (fun y => exp y) m_infty 0.
Proof.
evar_last.
apply is_lim_ext with (fun y => /(exp (- y))).
move => y ; rewrite exp_Ropp ; apply Rinv_involutive.
apply Rgt_not_eq, exp_pos.
apply is_lim_inv.
apply is_lim_comp with p_infty.
apply is_lim_exp_p.
replace p_infty with (Rbar_opp m_infty) by auto.
apply is_lim_opp.
apply is_lim_id.
by apply filter_forall.
by [].
by [].
