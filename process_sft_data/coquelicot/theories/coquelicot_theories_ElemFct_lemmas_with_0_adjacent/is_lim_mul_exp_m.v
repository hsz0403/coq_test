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

Lemma is_lim_mul_exp_m : is_lim (fun y => y * exp y) m_infty 0.
Proof.
evar_last.
apply is_lim_ext_loc with (fun y => - / (exp (-y) / (- y))).
exists 0 => y Hy.
rewrite exp_Ropp.
field.
split.
apply Rgt_not_eq, exp_pos.
by apply Rlt_not_eq.
apply is_lim_opp.
apply is_lim_inv.
apply (is_lim_comp (fun y => exp y / y)) with p_infty.
by apply is_lim_div_exp_p.
evar_last.
apply is_lim_opp.
apply is_lim_id.
by [].
by apply filter_forall.
by [].
simpl ; by rewrite Ropp_0.
