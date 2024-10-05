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

Lemma is_derive_sqrt (f : R -> R) (x df : R) : is_derive f x df -> 0 < f x -> is_derive (fun x => sqrt (f x)) x (df / (2 * sqrt (f x))).
Proof.
intros Hf Hfx.
evar_last.
eapply is_derive_comp.
by apply filterdiff_sqrt.
by apply Hf.
Admitted.

Lemma nat_to_ring_O : nat_to_ring O = zero.
Proof.
Admitted.

Lemma nat_to_ring_Sn (n : nat) : nat_to_ring (S n) = plus (nat_to_ring n) one.
Proof.
case: n => [ | n] ; rewrite /nat_to_ring.
rewrite sum_n_n sum_n_m_zero //.
by rewrite plus_zero_l.
rewrite sum_n_Sm //.
Admitted.

Lemma is_derive_mult (f g : K -> K) x (df dg : K) : is_derive f x df -> is_derive g x dg -> (forall n m : K, mult n m = mult m n) -> is_derive (fun x : K => mult (f x) (g x)) x (plus (mult df (g x)) (mult (f x) dg)).
Proof.
intros Hf Hg Hmult.
eapply filterdiff_ext_lin.
eapply filterdiff_comp_2 => /=.
by apply Hf.
by apply Hg.
eapply filterdiff_ext_lin.
apply (filterdiff_mult (f x,g x)) => /=.
intros P [d Hd].
assert (Cf := ex_derive_continuous f x).
assert (Cg := ex_derive_continuous g x).
destruct (fun H => proj1 (filterlim_locally _ _) (Cf H) d) as [d1 Hd1].
eexists ; by apply Hf.
destruct (fun H => proj1 (filterlim_locally _ _) (Cg H) d) as [d2 Hd2].
eexists ; by apply Hg.
exists (mkposreal _ (Rmin_stable_in_posreal d1 d2)) => /= y Hy.
apply Hd ; split => /=.
eapply (Hd1 y), ball_le, Hy.
by apply Rmin_l.
eapply (Hd2 y), ball_le, Hy.
by apply Rmin_r.
by apply Hmult.
simpl => [[y1 y2]] /=.
reflexivity.
simpl => y.
rewrite /scal /=.
rewrite mult_assoc (Hmult (f x)) -!mult_assoc.
Admitted.

Lemma filterdiff_pow_n {K : AbsRing} (x : K) (n : nat) : (forall a b : K, mult a b = mult b a) -> filterdiff (fun y : K => pow_n y n) (locally x) (fun y : K => scal y (mult (nat_to_ring n) (pow_n x (pred n)))).
Proof.
intros Hmult.
rewrite -/(is_derive (fun y : K => pow_n y n) x (mult (nat_to_ring n) (pow_n x (pred n)))).
elim: n => [ | n IH] /=.
evar_last.
apply is_derive_const.
by rewrite nat_to_ring_O mult_zero_l.
evar_last.
eapply is_derive_mult.
apply is_derive_id.
apply IH.
by apply Hmult.
simpl.
rewrite nat_to_ring_Sn mult_one_l mult_assoc (Hmult x) -mult_assoc.
rewrite mult_distr_r mult_one_l plus_comm.
apply f_equal2 => //.
clear ; case: n => [ | n] //=.
Admitted.

Lemma is_derive_n_pow_smalli: forall i p x, (i <= p)%nat -> is_derive_n (fun x : R => x ^ p) i x (INR (fact p) / INR (fact (p - i)%nat) * x ^ (p - i)%nat).
Proof.
elim => /= [ | i IH] p x Hip.
rewrite -minus_n_O ; field.
by apply INR_fact_neq_0.
eapply is_derive_ext.
intros t.
apply sym_equal, is_derive_n_unique, IH.
eapply le_trans, Hip ; by apply le_n_Sn.
evar_last.
apply is_derive_scal, is_derive_pow, is_derive_id.
rewrite MyNat.sub_succ_r.
change one with 1.
rewrite {1 2} (S_pred (p - i) O) /fact -/fact ?mult_INR.
field.
split.
apply INR_fact_neq_0.
apply not_0_INR, sym_not_eq, O_S.
Admitted.

Lemma Derive_n_pow_smalli: forall i p x, (i <= p)%nat -> Derive_n (fun x : R => x ^ p) i x = INR (fact p) / INR (fact (p - i)%nat) * x ^ (p - i)%nat.
Proof.
intros.
Admitted.

Lemma is_derive_n_pow_bigi: forall i p x, (p < i) %nat -> is_derive_n (fun x : R => x ^ p) i x 0.
Proof.
elim => /= [ | i IH] p x Hip.
by apply lt_n_O in Hip.
apply lt_n_Sm_le, le_lt_eq_dec in Hip.
case: Hip => [Hip | ->] ; eapply is_derive_ext.
intros t ; by apply sym_equal, is_derive_n_unique, IH.
apply @is_derive_const.
intros t ; rewrite Derive_n_pow_smalli.
by rewrite minus_diag /=.
by apply le_refl.
Admitted.

Lemma Derive_n_pow_bigi: forall i p x, (p < i) %nat -> Derive_n (fun x : R => x ^ p) i x = 0.
Proof.
intros.
Admitted.

Lemma Derive_n_pow i p x: Derive_n (fun x : R => x ^ p) i x = match (le_dec i p) with | left _ => INR (fact p) / INR (fact (p -i)%nat) * x ^ (p - i)%nat | right _ => 0 end.
Proof.
case: le_dec => H.
by apply Derive_n_pow_smalli.
Admitted.

Lemma ex_derive_n_pow i p x: ex_derive_n (fun x : R => x ^ p) i x.
Proof.
case: i => //= i.
exists (Derive_n (fun x : R => x ^ p) (S i) x).
rewrite Derive_n_pow.
case: le_dec => Hip.
by apply (is_derive_n_pow_smalli (S i)).
Admitted.

Lemma is_RInt_pow : forall a b n, is_RInt (fun x => pow x n) a b (pow b (S n) / INR (S n) - pow a (S n) / INR (S n)).
Proof.
intros a b n.
set f := fun x => pow x (S n) / INR (S n).
fold (f a) (f b).
assert (H: forall x : R, is_derive f x (pow x n)).
intros x.
evar_last.
rewrite /f /Rdiv -[Rmult]/(scal (V := R_NormedModule)).
apply is_derive_scal_l.
apply is_derive_pow, is_derive_id.
rewrite /pred.
set k := INR (S n).
rewrite /scal /= /mult /one /=.
field.
rewrite /k S_INR.
apply Rgt_not_eq, INRp1_pos.
apply: is_RInt_derive => x Hx //.
apply continuity_pt_filterlim.
apply derivable_continuous_pt.
Admitted.

Lemma exp_ge_taylor (x : R) (n : nat) : 0 <= x -> sum_f_R0 (fun k => x^k / INR (fact k)) n <= exp x.
Proof.
move => Hx.
rewrite /exp /exist_exp.
case: Alembert_C3 => /= y Hy.
apply Rnot_lt_le => H.
apply Rminus_lt_0 in H.
case: (Hy _ H) => N {Hy} Hy.
move: (Hy _ (le_plus_r n N)) => {Hy}.
apply Rle_not_lt.
apply Rle_trans with (2 := Rle_abs _).
apply Rplus_le_compat_r.
elim: N => [ | N IH].
rewrite plus_0_r.
apply Req_le.
elim: (n) => {n H} [ | n /= <-].
apply Rmult_comm.
apply f_equal.
apply Rmult_comm.
apply Rle_trans with (1 := IH).
rewrite -plus_n_Sm.
move: (n + N)%nat => {n H N IH} n.
rewrite /sum_f_R0 -/sum_f_R0.
apply Rminus_le_0 ; ring_simplify.
apply Rmult_le_pos.
apply Rlt_le, Rinv_0_lt_compat, INR_fact_lt_0.
Admitted.

Lemma is_exp_Reals (x : R) : is_pseries (fun n => / INR (fact n)) x (exp x).
Proof.
rewrite /exp.
case: exist_exp => l /= Hl.
apply Series.is_series_Reals in Hl.
move: Hl ; apply Series.is_series_ext => n.
Admitted.

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
