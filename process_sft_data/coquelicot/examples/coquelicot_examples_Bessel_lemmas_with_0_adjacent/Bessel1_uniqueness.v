Require Import Reals Psatz.
Require Import mathcomp.ssreflect.ssreflect.
Require Import Rcomplements Rbar Hierarchy.
Require Import Derive Series PSeries Lim_seq.
Require Import AutoDerive.
Definition Bessel1_seq (n k : nat) := (-1)^(k)/(INR (fact (k)) * INR (fact (n + (k)))).
Definition Bessel1 (n : nat) (x : R) := (x/2)^n * PSeries (Bessel1_seq n) ((x/2)^2).

Lemma Bessel1_uniqueness (a : nat -> R) (n : nat) : (Rbar_lt 0 (CV_radius a)) -> (forall x : R, x^2 * Derive_n (PSeries a) 2 x + x * Derive (PSeries a) x + (x^2 - (INR n)^2) * PSeries a x = 0) -> {b : R | forall x, PSeries a x = b * Bessel1 n x}.
Proof.
intros Hcv_a Ha.
assert ((a 0%nat = 0 \/ n = O) /\ (a 1%nat = 0 \/ n = 1%nat) /\ (forall k, (INR (S (S k)) ^ 2 - INR n ^ 2) * a (S (S k)) + a k = 0)).
by apply Bessel1_uniqueness_aux_0.
assert ((forall k : nat, (k < n)%nat -> a k = 0) /\ (forall p : nat, a (n + 2 * p + 1)%nat = 0) /\ (forall p : nat, a (n + 2 * p)%nat = Bessel1_seq n p * / 2 ^ (2 * p) * INR (fact n) * a n)).
apply Bessel1_uniqueness_aux_1 ; by apply H.
exists (2^n * INR (fact n) * a n) => x.
rewrite /Bessel1 (PSeries_decr_n_aux _ n).
case: H0 => _ H0.
rewrite Rpow_mult_distr -Rinv_pow.
field_simplify ; rewrite ?Rdiv_1.
rewrite !(Rmult_assoc (x ^ n)).
apply Rmult_eq_compat_l.
rewrite PSeries_odd_even.
replace (PSeries (fun n0 : nat => PS_decr_n a n (2 * n0 + 1)) (x ^ 2)) with 0.
case: H0 => _ H0.
rewrite Rmult_0_r Rplus_0_r.
rewrite -PSeries_scal.
apply Series_ext => k.
rewrite /PS_decr_n /PS_scal.
rewrite H0.
rewrite -!pow_mult.
rewrite Rpow_mult_distr -Rinv_pow.
rewrite /scal /= /mult /=.
ring.
by apply Rgt_not_eq, Rlt_0_2.
apply sym_eq.
rewrite -(PSeries_const_0 (x^2)).
apply PSeries_ext => k.
rewrite /PS_decr_n.
replace (n + (2 * k + 1))%nat with (n + 2 * k + 1)%nat by ring.
by apply H0.
eapply ex_pseries_ext.
move => p ; apply sym_eq.
apply H0.
eapply ex_pseries_ext.
intros p ; rewrite Rmult_assoc ; apply Rmult_comm.
apply @ex_pseries_scal.
by apply Rmult_comm.
case: (Req_dec x 0) => Hx0.
rewrite Hx0.
rewrite /= Rmult_0_l.
by apply @ex_pseries_0.
apply ex_series_Rabs.
apply ex_series_DAlembert with 0.
by apply Rlt_0_1.
intros p.
apply Rmult_integral_contrapositive_currified.
rewrite pow_n_pow.
by apply pow_nonzero, pow_nonzero.
apply Rmult_integral_contrapositive_currified.
by apply Bessel1_seq_neq_0.
apply Rinv_neq_0_compat.
apply pow_nonzero.
by apply Rgt_not_eq, Rlt_0_2.
apply is_lim_seq_ext with (fun p => x^2 / 4 * / (INR (S p) * INR (S (n + p)))).
intros p ; rewrite !pow_n_pow !pow_mult.
rewrite /Bessel1_seq -plus_n_Sm /fact -/fact !mult_INR.
replace (@scal R_AbsRing R_NormedModule) with Rmult by auto.
simpl (_^(S p)) ; rewrite -!/(pow _ 2) ; ring_simplify (2^2).
field_simplify (x ^ 2 * (x ^ 2) ^ p * (-1 * (-1) ^ p / (INR (S p) * INR (fact p) * (INR (S (n + p)) * INR (fact (n + p)))) * / (4 * 4 ^ p)) / ((x ^ 2) ^ p * ((-1) ^ p / (INR (fact p) * INR (fact (n + p))) * / 4 ^ p))).
rewrite Rabs_div.
rewrite Rabs_Ropp /Rdiv !Rabs_pos_eq.
field.
split ; apply (not_INR _ 0), sym_not_eq, O_S.
change 4 with (INR 2 * INR 2).
repeat apply Rmult_le_pos ; apply pos_INR.
by apply pow2_ge_0.
change 4 with (INR 2 * INR 2).
apply Rgt_not_eq ; repeat apply Rmult_lt_0_compat ; apply lt_0_INR, lt_O_Sn.
repeat split.
apply pow_nonzero, Rgt_not_eq ; repeat apply Rmult_lt_0_compat ; apply Rlt_0_2.
by apply INR_fact_neq_0.
by apply INR_fact_neq_0.
by apply Rgt_not_eq, lt_0_INR, lt_O_Sn.
by apply Rgt_not_eq, lt_0_INR, lt_O_Sn.
by apply pow_nonzero, Rlt_not_eq, (IZR_lt (-1) 0).
rewrite -pow_mult ; by apply pow_nonzero.
evar_last.
apply is_lim_seq_scal_l.
apply is_lim_seq_inv.
eapply is_lim_seq_mult.
apply -> is_lim_seq_incr_1.
by apply is_lim_seq_INR.
apply is_lim_seq_ext with (fun k => INR (k + S n)).
intros k.
by rewrite (Plus.plus_comm n k) plus_n_Sm.
apply is_lim_seq_incr_n.
by apply is_lim_seq_INR.
by [].
by [].
simpl ; apply f_equal ; ring.
apply ex_pseries_ext with (fun _ => 0).
intros k.
rewrite /PS_decr_n /=.
replace (n + (k + (k + 0) + 1))%nat with (n + 2 * k + 1)%nat by ring.
by rewrite (proj1 H0).
eapply ex_series_ext.
intros k.
rewrite /scal /= /mult /= Rmult_0_r.
reflexivity.
exists 0 ; apply filterlim_ext with (fun _ => 0).
elim => /= [ | k IH].
by rewrite sum_O.
by rewrite sum_Sn plus_zero_r.
by apply filterlim_const.
by apply pow_nonzero, Rgt_not_eq, Rlt_0_2.
by apply Rgt_not_eq, Rlt_0_2.
by apply H0.
