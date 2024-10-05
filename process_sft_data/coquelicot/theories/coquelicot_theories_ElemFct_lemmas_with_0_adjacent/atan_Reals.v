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

Lemma atan_Reals (x : R) : Rabs x < 1 -> atan x = x * PSeries (fun n => (-1)^n / (INR (S (n + n)))) (x ^ 2).
Proof.
wlog: x / (0 <= x) => [Hw | Hx0] Hx.
case: (Rle_lt_dec 0 x) => Hx0.
by apply Hw.
rewrite -{1}(Ropp_involutive x) atan_opp Hw.
replace ((- x) ^ 2) with (x^2) by ring.
ring.
apply Ropp_le_cancel ; rewrite Ropp_involutive Ropp_0 ; by left.
by rewrite Rabs_Ropp.
rewrite Rabs_pos_eq // in Hx.
case: Hx0 => Hx0.
rewrite atan_eq_ps_atan ; try by split.
rewrite /ps_atan.
case: Ratan.in_int => H.
case: ps_atan_exists_1 => ps Hps.
apply sym_eq.
rewrite -Series.Series_scal_l.
apply Series.is_series_unique.
apply is_lim_seq_Reals in Hps.
move: Hps ; apply is_lim_seq_ext => n.
rewrite -sum_n_Reals.
apply sum_n_ext => k.
rewrite /tg_alt /Ratan_seq S_INR !plus_INR.
rewrite pow_add -pow_mult.
simpl ; field.
rewrite -plus_INR -S_INR.
apply Rgt_not_eq, (lt_INR 0), lt_O_Sn.
contradict H ; split.
apply Rle_trans with 0.
apply Rminus_le_0 ; ring_simplify ; by apply Rle_0_1.
by left.
by left.
by rewrite -Hx0 atan_0 Rmult_0_l.
