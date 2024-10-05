Require Import Reals Psatz.
Require Import mathcomp.ssreflect.ssreflect.
Require Import Rcomplements Rbar Hierarchy.
Require Import Derive Series PSeries Lim_seq.
Require Import AutoDerive.
Definition Bessel1_seq (n k : nat) := (-1)^(k)/(INR (fact (k)) * INR (fact (n + (k)))).
Definition Bessel1 (n : nat) (x : R) := (x/2)^n * PSeries (Bessel1_seq n) ((x/2)^2).

Lemma Bessel1_correct (n : nat) (x : R) : x^2 * Derive_n (Bessel1 n) 2 x + x * Derive (Bessel1 n) x + (x^2 - (INR n)^2) * Bessel1 n x = 0.
Proof.
rewrite (is_derive_unique _ _ _ (is_derive_Bessel1 _ _)) ; rewrite /Derive_n (is_derive_unique _ _ _ (is_derive_2_Bessel1 _ _)) ; rewrite /Bessel1 plus_INR ?mult_INR ; simpl INR.
set y := x/2 ; replace x with (2 * y) by (unfold y ; field).
replace (_ + _) with (4 * y^S (S n) * (y^2 * PSeries (PS_derive (PS_derive (Bessel1_seq n))) (y ^ 2) + (INR n + 1) * PSeries (PS_derive (Bessel1_seq n)) (y ^ 2) + PSeries (Bessel1_seq n) (y ^ 2))).
Focus 2.
case: n => [|[|n]] ; rewrite ?S_INR /= ; field.
apply Rmult_eq_0_compat_l.
rewrite -PSeries_incr_1 -PSeries_scal -?PSeries_plus.
unfold PS_derive, PS_incr_1, PS_scal, PS_plus.
rewrite -(PSeries_const_0 (y^2)).
apply PSeries_ext.
case => [ | p] ; rewrite /Bessel1_seq ; rewrite -?plus_n_Sm ?plus_0_r /fact -/fact ?mult_INR ?S_INR ?plus_INR ; simpl INR ; simpl pow ; rewrite ?Rplus_0_l ?Rmult_1_l.
rewrite /plus /zero /scal /= /mult /=.
field.
split ; rewrite -?S_INR ; apply Rgt_not_eq.
by apply INR_fact_lt_0.
by apply (lt_INR 0), lt_O_Sn.
rewrite /plus /scal /= /mult /=.
field.
repeat split ; rewrite -?plus_INR -?S_INR ; apply Rgt_not_eq.
by apply INR_fact_lt_0.
by apply (lt_INR 0), lt_O_Sn.
by apply INR_fact_lt_0.
by apply (lt_INR 0), lt_O_Sn.
by apply (lt_INR 0), lt_O_Sn.
by apply (lt_INR 0), lt_O_Sn.
apply CV_radius_inside.
apply Rbar_lt_le_trans with (2 := CV_radius_plus _ _).
apply Rbar_min_case.
by rewrite CV_radius_incr_1 ?CV_radius_derive CV_Bessel1.
rewrite CV_radius_scal.
by rewrite CV_radius_derive CV_Bessel1.
now rewrite -S_INR ; apply not_0_INR, sym_not_eq, O_S.
by apply ex_Bessel1.
apply ex_pseries_R, ex_series_Rabs, CV_disk_inside.
by rewrite CV_radius_incr_1 ?CV_radius_derive CV_Bessel1.
apply ex_pseries_R, ex_series_Rabs, CV_disk_inside.
rewrite CV_radius_scal.
by rewrite CV_radius_derive CV_Bessel1.
now rewrite -S_INR ; apply not_0_INR, sym_not_eq, O_S.
