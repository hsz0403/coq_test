Require Import Reals Even Div2 Omega Psatz.
Require Import mathcomp.ssreflect.ssreflect.
Require Import Rcomplements Rbar Lim_seq Lub Hierarchy.
Require Import Continuity Derive Seq_fct Series.
Section Definitions.
Context {K : AbsRing} {V : NormedModule K}.
Definition is_pseries (a : nat -> V) (x:K) (l : V) := is_series (fun k => scal (pow_n x k) (a k)) l.
Definition ex_pseries (a : nat -> V) (x : K) := ex_series (fun k => scal (pow_n x k) (a k)).
End Definitions.
Definition PSeries (a : nat -> R) (x : R) : R := Series (fun k => a k * x ^ k).
Section Extensionality.
Context {K : AbsRing} {V : NormedModule K}.
End Extensionality.
Section ConvergenceCircle.
Context {K : AbsRing} {V : NormedModule K}.
End ConvergenceCircle.
Definition CV_disk (a : nat -> R) (r : R) := ex_series (fun n => Rabs (a n * r^n)).
Definition CV_radius (a : nat -> R) : Rbar := Lub_Rbar (CV_disk a).
Section PS_plus.
Context {K : AbsRing} {V : NormedModule K}.
Definition PS_plus (a b : nat -> V) (n : nat) : V := plus (a n) (b n).
End PS_plus.
Section PS_scal.
Context {K : AbsRing} {V : NormedModule K}.
Definition PS_scal (c : K) (a : nat -> V) (n : nat) : V := scal c (a n).
End PS_scal.
Definition PS_scal_r (c : R) (a : nat -> R) (n : nat) : R := a n * c.
Section PS_incr.
Context {K : AbsRing} {V : NormedModule K}.
Definition PS_incr_1 (a : nat -> V) (n : nat) : V := match n with | 0 => zero | S n => a n end.
Fixpoint PS_incr_n (a : nat -> V) (n k : nat) : V := match n with | O => a k | S n => PS_incr_1 (PS_incr_n a n) k end.
Definition PS_decr_1 (a : nat -> V) (n : nat) : V := a (S n).
Definition PS_decr_n (a : nat -> V) (n k : nat) : V := a (n + k)%nat.
End PS_incr.
Definition PS_mult (a b : nat -> R) n := sum_f_R0 (fun k => a k * b (n - k)%nat) n.
Section PS_opp.
Context {K : AbsRing} {V : NormedModule K}.
Definition PS_opp (a : nat -> V) (n : nat) : V := opp (a n).
End PS_opp.
Section PS_minus.
Context {K : AbsRing} {V : NormedModule K}.
Definition PS_minus (a b : nat -> V) (n : nat) : V := plus (a n) (opp (b n)).
End PS_minus.
Definition PS_derive (a : nat -> R) (n : nat) := INR (S n) * a (S n).
Definition PS_derive_n (n : nat) (a : nat -> R) := (fun k => (INR (fact (k + n)%nat) / INR (fact k)) * a (k + n)%nat).

Lemma Abel (a : nat -> R) : Rbar_lt 0 (CV_radius a) -> Rbar_lt (CV_radius a) p_infty -> ex_pseries a (CV_radius a) -> filterlim (PSeries a) (at_left (CV_radius a)) (locally (PSeries a (CV_radius a))).
Proof.
case Hcv : (CV_radius a) => [cv | | ] //= Hcv0 _ Ha1.
wlog: cv a Hcv Hcv0 Ha1 / (cv = 1) => Hw.
apply filterlim_ext with (fun x => PSeries (fun n => a n * cv ^ n) (x / cv)).
intros x.
apply Series_ext => n.
rewrite Rmult_assoc -Rpow_mult_distr.
apply f_equal, f_equal2 => //.
field ; by apply Rgt_not_eq.
apply filterlim_comp with (at_left 1).
intros P [d Hd].
unfold filtermap.
eapply filter_imp.
intros x Hx ; apply Hd.
apply @norm_compat1.
rewrite /minus /plus /opp /=.
replace (x / cv + _) with ((x - cv) / cv) by (field ; exact: Rgt_not_eq).
rewrite /norm /= /abs /= Rabs_div ; try by apply Rgt_not_eq.
rewrite (Rabs_pos_eq cv) ; try by apply Rlt_le.
apply Rlt_div_l => //.
eapply (proj1 Hx).
apply Rlt_div_l => //.
rewrite Rmult_1_l.
by apply (proj2 Hx).
assert (Hd' : 0 < d * cv).
apply Rmult_lt_0_compat.
by apply d.
by [].
exists (mkposreal _ Hd') => /= y Hy Hy0 ; by split.
replace (PSeries a cv) with (PSeries (fun n : nat => a n * cv ^ n) 1).
apply (Hw 1 (fun n : nat => a n * cv ^ n)) ; clear Hw.
apply Rbar_le_antisym.
move: Hcv ; rewrite /CV_radius /Lub.Lub_Rbar /CV_disk.
case: Lub.ex_lub_Rbar => l /= Hl Hl1 ; case: Lub.ex_lub_Rbar => l' /= Hl'.
rewrite Hl1 in Hl => {l Hl1}.
apply Hl'.
intros x Hx.
apply (Rmult_le_reg_l cv) => //.
rewrite Rmult_1_r.
apply Hl.
move: Hx ; apply ex_series_ext => n.
by rewrite Rpow_mult_distr Rmult_assoc.
rewrite -Rabs_R1.
apply Rbar_not_lt_le => Hcv'.
apply CV_disk_outside in Hcv'.
apply: Hcv'.
apply ex_series_lim_0 ; move: Ha1 ; apply ex_series_ext => n.
rewrite pow_n_pow pow1 Rmult_1_r.
apply Rmult_comm.
by apply Rlt_0_1.
move: Ha1 ; apply ex_series_ext => n.
rewrite !pow_n_pow pow1 scal_one.
apply Rmult_comm.
by [].
apply Series_ext => n.
by rewrite pow1 Rmult_1_r.
rewrite Hw in Hcv Ha1 |- * => {cv Hw Hcv0}.
wlog: a Hcv Ha1 / (PSeries a 1 = 0) => Hw.
set b := fun n => match n with | O => a O - PSeries a 1 | S n => a (S n) end.
assert (CV_radius b = Finite 1).
rewrite -Hcv.
rewrite -(CV_radius_decr_1 a) -(CV_radius_decr_1 b).
apply CV_radius_ext => n.
reflexivity.
assert (ex_pseries b 1).
apply ex_series_incr_1.
apply ex_series_incr_1 in Ha1.
move: Ha1 ; apply ex_series_ext => n.
reflexivity.
assert (PSeries b 1 = 0).
rewrite PSeries_decr_1 //.
rewrite /b PSeries_decr_1 /PS_decr_1 //.
ring.
specialize (Hw b H H0 H1).
apply filterlim_ext_loc with (fun x => PSeries b x + PSeries a 1).
exists (mkposreal _ Rlt_0_1) => x Hx0 Hx.
apply (Rabs_lt_between' x 1 1) in Hx0.
rewrite Rminus_eq_0 in Hx0.
rewrite PSeries_decr_1.
rewrite /b (PSeries_decr_1 a x) /PS_decr_1.
ring.
apply CV_radius_inside.
rewrite Hcv Rabs_pos_eq.
by [].
by apply Rlt_le, Hx0.
apply CV_radius_inside.
rewrite H Rabs_pos_eq.
by [].
by apply Rlt_le, Hx0.
rewrite -{2}(Rplus_0_l (PSeries a 1)).
eapply filterlim_comp_2.
by apply Hw.
by apply filterlim_const.
rewrite H1.
apply @filterlim_plus.
apply PSeries_correct in Ha1.
rewrite Hw in Ha1 |- * => {Hw}.
set Sa := sum_n a.
assert (forall n x, sum_n (fun k => scal (pow_n x k) (a k)) n = (1 - x) * sum_n (fun k => scal (pow_n x k) (Sa k)) n + scal (pow_n x (S n)) (Sa n)).
elim => /= [ | n IH] x.
rewrite /Sa !sum_O scal_one mult_one_r /=.
rewrite /scal /= /mult /= ; ring.
rewrite !sum_Sn IH ; clear IH.
rewrite /Sa /= !sum_Sn -/(Sa n).
rewrite /plus /scal /= /mult /=.
ring.
assert (forall x, Rabs x < 1 -> is_pseries Sa x (PSeries a x / (1 - x))).
intros x Hx.
destruct (CV_radius_inside a x) as [l Hl].
rewrite Hcv.
by apply Hx.
rewrite (is_pseries_unique _ _ _ Hl).
rewrite /is_pseries /is_series.
replace (@locally R_NormedModule (l / (1 - x))) with (Rbar_locally (Rbar_mult (l - ((Rbar_mult x 0) * 0)) (/ (1 - x)))).
apply (is_lim_seq_ext (fun n => (sum_n (fun k : nat => scal (pow_n (K := R_AbsRing) x k) (a k)) n - scal (pow_n (K := R_AbsRing) x (S n)) (Sa n)) / (1 - x)) (sum_n (fun k : nat => scal (pow_n (K := R_AbsRing) x k) (Sa k)))).
intros n ; rewrite H.
field.
apply Rgt_not_eq ; apply -> Rminus_lt_0.
by apply Rabs_lt_between, Hx.
apply is_lim_seq_scal_r.
apply is_lim_seq_minus'.
apply Hl.
apply is_lim_seq_mult'.
apply is_lim_seq_mult'.
apply is_lim_seq_const.
eapply is_lim_seq_ext.
intros n ; by apply sym_eq, pow_n_pow.
apply is_lim_seq_geom.
by apply Hx.
move: Ha1 ; apply (is_lim_seq_ext _ _ 0).
intros n ; apply sum_n_ext => k.
by rewrite pow_n_pow pow1 scal_one.
by replace (Rbar_mult (l - Rbar_mult x 0 * 0) (/ (1 - x))) with (Finite (l / (1 - x))) by (simpl ; apply f_equal ; unfold Rdiv ; ring).
apply filterlim_ext_loc with (fun x => (1-x) * PSeries Sa x).
exists (mkposreal _ Rlt_0_1) ; simpl ; intros x Hx Hx1.
apply (Rabs_lt_between' x 1 1) in Hx.
rewrite Rminus_eq_0 in Hx.
assert (Rabs x < 1).
rewrite Rabs_pos_eq.
by apply Hx1.
by apply Rlt_le, Hx.
specialize (H0 x H1).
rewrite (is_pseries_unique _ _ _ H0).
field.
by apply Rgt_not_eq ; apply -> Rminus_lt_0.
apply filterlim_locally => eps.
destruct (Ha1 (ball 0 (pos_div_2 eps))) as [N HN].
apply locally_ball.
eapply filter_imp.
intros x Hx.
rewrite (PSeries_decr_n _ N).
rewrite (double_var eps) Rmult_plus_distr_l.
eapply Rle_lt_trans.
rewrite /minus opp_zero plus_zero_r.
apply @abs_triangle.
rewrite /abs /= 3!Rabs_mult.
apply Rplus_lt_le_compat.
eapply Rle_lt_trans.
apply Rmult_le_compat_l.
by apply Rabs_pos.
eapply Rle_trans.
apply Rsum_abs.
apply sum_growing.
intros n.
rewrite Rabs_mult.
apply Rmult_le_compat_l.
by apply Rabs_pos.
rewrite -RPow_abs.
apply pow_incr ; split.
apply Rabs_pos.
apply Rlt_le.
instantiate (1 := 1).
eapply (proj1 Hx).
destruct Hx as [Hx1 Hx].
eapply Rle_lt_trans.
apply Rmult_le_compat_l.
by apply Rabs_pos.
apply (Rmax_r 1).
apply Rlt_div_r.
eapply Rlt_le_trans, Rmax_l.
by apply Rlt_0_1.
eapply (proj1 Hx).
destruct Hx as [Hx1 [Hx2 Hx]].
eapply Rle_trans.
apply Rmult_le_compat_l.
by apply Rabs_pos.
apply Rmult_le_compat ; try by apply Rabs_pos.
rewrite -/(pow _ (S N)) -RPow_abs.
apply pow_incr ; split.
apply Rabs_pos.
apply Rlt_le, Hx1.
eapply Rle_trans.
apply Series_Rabs.
eapply @ex_series_le.
intros n ; rewrite /norm /= /abs /= Rabs_Rabsolu.
rewrite Rabs_mult.
rewrite -RPow_abs.
apply Rmult_le_compat_r.
rewrite RPow_abs ; by apply Rabs_pos.
rewrite /PS_decr_n.
eapply Rle_trans, Rlt_le, HN.
apply Req_le, f_equal.
rewrite /minus opp_zero plus_zero_r.
apply sum_n_ext => k.
by rewrite pow_n_pow pow1 scal_one.
apply le_trans with (1 := le_n_Sn _).
apply le_plus_l.
apply @ex_series_scal.
apply ex_series_geom.
by rewrite Rabs_Rabsolu.
apply Series_le.
intros n ; split.
apply Rabs_pos.
rewrite Rabs_mult.
rewrite -RPow_abs.
apply Rmult_le_compat_r.
rewrite RPow_abs ; by apply Rabs_pos.
rewrite /PS_decr_n.
eapply Rle_trans, Rlt_le, HN.
apply Req_le, f_equal.
rewrite /minus opp_zero plus_zero_r.
apply sum_n_ext => k.
by rewrite pow_n_pow pow1 scal_one.
apply le_trans with (1 := le_n_Sn _).
apply le_plus_l.
apply @ex_series_scal.
apply ex_series_geom.
by rewrite Rabs_Rabsolu.
rewrite Series_scal_l Series_geom.
rewrite pow1 Rmult_1_l !Rabs_pos_eq.
apply Req_le ; simpl ; field.
apply Rgt_not_eq ; apply -> Rminus_lt_0.
eapply Rle_lt_trans, Hx1.
by apply Rle_abs.
apply Hx.
apply -> Rminus_le_0.
eapply Rle_trans, Rlt_le, Hx1.
by apply Rle_abs.
by rewrite Rabs_Rabsolu.
eexists ; apply H0, Hx.
assert (0 < Rmin (eps / 2 / Rmax 1 (sum_f_R0 (fun n : nat => Rabs (Sa n) * 1 ^ n) N)) 1).
apply Rmin_case.
apply Rdiv_lt_0_compat.
by apply is_pos_div_2.
eapply Rlt_le_trans, Rmax_l.
by apply Rlt_0_1.
by apply Rlt_0_1.
exists (mkposreal _ H1) => /= y Hy Hy1.
split.
apply (Rabs_lt_between' y 1 (Rmin (eps / 2 / Rmax 1 (sum_f_R0 (fun n : nat => Rabs (Sa n) * 1 ^ n) N)) 1)) in Hy.
rewrite {1}/Rminus -Rmax_opp_Rmin Rplus_max_distr_l Rplus_min_distr_l in Hy.
rewrite -!/(Rminus _ _) Rminus_eq_0 in Hy.
rewrite Rabs_pos_eq.
by [].
apply Rlt_le.
eapply Rle_lt_trans, Hy.
by apply Rmax_r.
split.
eapply Rlt_le_trans.
rewrite -Rabs_Ropp Ropp_minus_distr'.
apply Hy.
by apply Rmin_l.
apply (Rabs_lt_between' y 1 (Rmin (eps / 2 / Rmax 1 (sum_f_R0 (fun n : nat => Rabs (Sa n) * 1 ^ n) N)) 1)) in Hy.
rewrite {1}/Rminus -Rmax_opp_Rmin Rplus_max_distr_l Rplus_min_distr_l in Hy.
rewrite -!/(Rminus _ _) Rminus_eq_0 in Hy.
eapply Rle_trans, Rlt_le, Hy.
by apply Rmax_r.
