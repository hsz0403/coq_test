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

Lemma is_lim_div_exp_p : is_lim (fun y => exp y / y) p_infty p_infty.
Proof.
apply is_lim_le_p_loc with (fun y => (1 + y + y^2 / 2)/y).
exists 0 => y Hy.
apply Rmult_le_compat_r.
by apply Rlt_le, Rinv_0_lt_compat.
rewrite /exp.
rewrite /exist_exp.
case: Alembert_C3 => /= x Hx.
rewrite /Pser /infinite_sum in Hx.
apply Rnot_lt_le => H.
case: (Hx _ (proj1 (Rminus_lt_0 _ _) H)) => N {Hx} Hx.
move: (Hx _ (le_plus_r 2 N)) => {Hx}.
apply Rle_not_lt.
apply Rle_trans with (2 := Rle_abs _).
apply Rplus_le_compat_r.
elim: N => [ | n IH].
simpl ; apply Req_le ; field.
apply Rle_trans with (1 := IH).
rewrite -plus_n_Sm ; move: (2 + n)%nat => {n IH} n.
rewrite /sum_f_R0 -/sum_f_R0.
rewrite Rplus_comm ; apply Rle_minus_l ; rewrite Rminus_eq_0.
apply Rmult_le_pos.
apply Rlt_le, Rinv_0_lt_compat, INR_fact_lt_0.
apply pow_le.
by apply Rlt_le.
apply is_lim_ext_loc with (fun y => /y + 1 + y / 2).
exists 0 => y Hy.
field.
by apply Rgt_not_eq.
eapply is_lim_plus.
eapply is_lim_plus.
apply is_lim_inv.
apply is_lim_id.
by [].
apply is_lim_const.
by [].
apply is_lim_div.
apply is_lim_id.
apply is_lim_const.
apply Rbar_finite_neq, Rgt_not_eq, Rlt_0_2.
simpl.
apply Rgt_not_eq, Rinv_0_lt_compat, Rlt_0_2.
simpl.
case: Rle_dec (Rlt_le _ _ (Rinv_0_lt_compat 2 (Rlt_0_2))) => //= H _.
case: Rle_lt_or_eq_dec (Rlt_not_eq _ _ (Rinv_0_lt_compat 2 (Rlt_0_2))) => //= H _.
