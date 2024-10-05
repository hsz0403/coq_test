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

Lemma exp_Reals (x : R) : exp x = PSeries (fun n => / INR (fact n)) x.
Proof.
apply sym_eq, is_pseries_unique.
Admitted.

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
Admitted.

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
Admitted.

Lemma ex_lim_exp (x : Rbar) : ex_lim (fun y => exp y) x.
Proof.
case: x => [x | | ].
apply ex_finite_lim_correct, ex_lim_continuity.
apply derivable_continuous_pt, derivable_pt_exp.
exists p_infty ; by apply is_lim_exp_p.
Admitted.

Lemma Lim_exp (x : Rbar) : Lim (fun y => exp y) x = match x with | Finite x => exp x | p_infty => p_infty | m_infty => 0 end.
Proof.
apply is_lim_unique.
case: x => [x | | ].
apply is_lim_continuity.
apply derivable_continuous_pt, derivable_pt_exp.
by apply is_lim_exp_p.
Admitted.

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
Admitted.

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
Admitted.

Lemma is_lim_div_expm1_0 : is_lim (fun y => (exp y - 1) / y) 0 1.
Proof.
apply is_lim_spec.
move => eps.
case: (derivable_pt_lim_exp_0 eps (cond_pos eps)) => delta H.
exists delta => y Hy Hy0.
rewrite /ball /= /AbsRing_ball /= /minus /plus /opp /= in Hy.
rewrite -/(Rminus _ _) Rminus_0_r in Hy.
move: (H y Hy0 Hy).
Admitted.

Lemma is_RInt_exp : forall a b, is_RInt exp a b (exp b - exp a).
Proof.
intros a b.
apply: is_RInt_derive.
intros x _.
apply is_derive_Reals, derivable_pt_lim_exp.
intros x _.
apply continuity_pt_filterlim.
apply derivable_continuous_pt.
Admitted.

Lemma is_lim_ln_p : is_lim (fun y => ln y) p_infty p_infty.
Proof.
apply is_lim_spec.
move => M.
exists (exp M) => x Hx.
rewrite -(ln_exp M).
apply ln_increasing.
apply exp_pos.
Admitted.

Lemma is_lim_div_ln_p : is_lim (fun y => ln y / y) p_infty 0.
Proof.
have H : forall x, 0 < x -> ln x < x.
move => x Hx.
apply Rminus_lt_0.
apply Rlt_le_trans with (1 := Rlt_0_1).
case: (MVT_gen (fun y => y - ln y) 1 x (fun y => (y-1)/y)).
move => z Hz.
evar (l : R).
replace ((z - 1) / z) with l.
apply is_derive_Reals.
apply derivable_pt_lim_minus.
apply derivable_pt_lim_id.
apply derivable_pt_lim_ln.
eapply Rlt_trans, Hz.
apply Rmin_case => //.
by apply Rlt_0_1.
rewrite /l ; field.
apply Rgt_not_eq ; eapply Rlt_trans, Hz.
apply Rmin_case => //.
by apply Rlt_0_1.
move => y Hy.
apply continuity_pt_minus.
apply continuity_pt_id.
apply derivable_continuous_pt ; eexists ; apply derivable_pt_lim_ln.
eapply Rlt_le_trans, Hy.
apply Rmin_case => //.
by apply Rlt_0_1.
move => c [Hc H0].
replace 1 with (1 - ln 1) by (rewrite ln_1 Rminus_0_r //).
apply Rminus_le_0.
rewrite H0.
move: Hc ; rewrite /Rmin /Rmax ; case: Rle_dec => H1 Hc.
apply Rmult_le_pos.
apply Rdiv_le_0_compat.
apply -> Rminus_le_0 ; apply Hc.
apply Rlt_le_trans with (1 := Rlt_0_1).
by apply Hc.
apply -> Rminus_le_0 ; apply H1.
apply Rnot_le_lt in H1.
replace ((c - 1) / c * (x - 1)) with ((1-c) * (1-x) / c).
apply Rdiv_le_0_compat.
apply Rmult_le_pos.
apply -> Rminus_le_0 ; apply Hc.
apply -> Rminus_le_0 ; apply Rlt_le, H1.
apply Rlt_le_trans with (1 := Hx).
by apply Hc.
field.
apply Rgt_not_eq.
apply Rlt_le_trans with (1 := Hx).
by apply Hc.
apply (is_lim_le_le_loc (fun _ => 0) (fun y => 2/sqrt y)).
exists 1 => x Hx.
split.
apply Rdiv_le_0_compat.
rewrite -ln_1.
apply ln_le.
apply Rlt_0_1.
by apply Rlt_le.
by apply Rlt_trans with (1 := Rlt_0_1).
replace (ln _) with (2 * ln (sqrt x)).
rewrite /Rdiv Rmult_assoc.
apply Rmult_le_compat_l.
apply Rlt_le, Rlt_0_2.
apply Rle_div_l.
by apply Rlt_trans with (1 := Rlt_0_1).
rewrite -{3}(sqrt_sqrt x).
field_simplify ; rewrite ?Rdiv_1.
apply Rlt_le, H.
apply sqrt_lt_R0.
by apply Rlt_trans with (1 := Rlt_0_1).
apply Rgt_not_eq.
apply sqrt_lt_R0.
by apply Rlt_trans with (1 := Rlt_0_1).
apply Rlt_le.
by apply Rlt_trans with (1 := Rlt_0_1).
change 2 with (INR 2).
rewrite -ln_pow.
rewrite /= Rmult_1_r.
rewrite sqrt_sqrt.
by [].
apply Rlt_le.
by apply Rlt_trans with (1 := Rlt_0_1).
apply sqrt_lt_R0.
by apply Rlt_trans with (1 := Rlt_0_1).
apply is_lim_const.
evar_last.
apply is_lim_div.
apply is_lim_const.
apply filterlim_sqrt_p.
by [].
by [].
Admitted.

Lemma is_lim_div_ln1p_0 : is_lim (fun y => ln (1+y) / y) 0 1.
Proof.
apply is_lim_spec.
move => eps.
case: (derivable_pt_lim_ln 1 (Rlt_0_1) eps (cond_pos eps)) => delta H.
exists delta => y Hy Hy0.
rewrite /ball /= /AbsRing_ball /= /minus /plus /opp /= in Hy.
rewrite /= -/(Rminus _ _) Rminus_0_r in Hy.
move: (H y Hy0 Hy).
Admitted.

Lemma is_lim_sinc_0 : is_lim (fun x => sin x / x) 0 1.
Proof.
apply is_lim_spec.
move => eps.
case: (derivable_pt_lim_sin_0 eps (cond_pos eps)) => delta H.
exists delta => y Hy Hy0.
rewrite /ball /= /AbsRing_ball /= /minus /plus /opp /= in Hy.
rewrite /= -/(Rminus _ _) Rminus_0_r in Hy.
move: (H y Hy0 Hy).
Admitted.

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
Admitted.

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
Admitted.

Lemma is_lim_ln_0 : filterlim ln (at_right 0) (Rbar_locally m_infty).
Proof.
intros P [M HM].
exists (mkposreal (exp M) (exp_pos _)) => x /= Hx Hx0.
apply HM.
rewrite <- (ln_exp M).
apply ln_increasing.
exact Hx0.
rewrite /ball /= /AbsRing_ball /= /abs /minus /plus /opp /= in Hx.
rewrite -/(Rminus _ _) Rminus_0_r Rabs_pos_eq in Hx.
exact Hx.
now apply Rlt_le.
