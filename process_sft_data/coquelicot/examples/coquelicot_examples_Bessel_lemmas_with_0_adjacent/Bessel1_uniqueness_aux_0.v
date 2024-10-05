Require Import Reals Psatz.
Require Import mathcomp.ssreflect.ssreflect.
Require Import Rcomplements Rbar Hierarchy.
Require Import Derive Series PSeries Lim_seq.
Require Import AutoDerive.
Definition Bessel1_seq (n k : nat) := (-1)^(k)/(INR (fact (k)) * INR (fact (n + (k)))).
Definition Bessel1 (n : nat) (x : R) := (x/2)^n * PSeries (Bessel1_seq n) ((x/2)^2).

Lemma Bessel1_uniqueness_aux_0 (a : nat -> R) (n : nat) : Rbar_lt 0 (CV_radius a) -> (forall x : R, Rbar_lt (Rabs x) (CV_radius a) -> x^2 * Derive_n (PSeries a) 2 x + x * Derive (PSeries a) x + (x^2 - (INR n)^2) * PSeries a x = 0) -> (a 0%nat = 0 \/ n = O) /\ (a 1%nat = 0 \/ n = 1%nat) /\ (forall k, (INR (S (S k)) ^ 2 - INR n ^ 2) * a (S (S k)) + a k = 0).
Proof.
move => Ha H.
cut (forall k, (PS_plus (PS_plus (PS_incr_n (PS_derive_n 2 a) 2) (PS_incr_1 (PS_derive a))) (PS_plus (PS_incr_n a 2) (PS_scal (- INR n ^ 2) a))) k = 0).
intros Haux.
split ; [move: (Haux 0%nat) | move: (fun k => Haux (S k))] => {Haux} Haux.
rewrite /PS_plus /= /PS_incr_1 /PS_derive_n /PS_scal /PS_derive in Haux.
rewrite /plus /zero /scal /= /mult /= in Haux.
ring_simplify in Haux.
apply Rmult_integral in Haux ; case: Haux => Haux.
right.
suff : ~ n <> 0%nat.
by intuition.
contradict Haux.
apply Ropp_neq_0_compat.
apply pow_nonzero.
by apply not_0_INR.
by left.
split ; [move: (Haux 0%nat) | move: (fun k => Haux (S k))] => {Haux} Haux.
rewrite /PS_plus /= /PS_incr_1 /PS_derive_n /PS_scal /PS_derive /= in Haux.
rewrite /plus /zero /scal /= /mult /= in Haux.
ring_simplify in Haux.
replace (- a 1%nat * INR n ^ 2 + a 1%nat) with ((1 - INR n ^ 2) * a 1%nat) in Haux.
apply Rmult_integral in Haux ; case: Haux => Haux.
right.
suff : ~ n <> 1%nat.
by intuition.
contradict Haux.
replace (1 - INR n ^ 2) with ((1-INR n) * (1 + INR n)) by ring.
apply Rmult_integral_contrapositive_currified.
apply Rminus_eq_contra.
apply sym_not_eq.
by apply not_1_INR.
apply Rgt_not_eq, Rlt_le_trans with (1 := Rlt_0_1).
apply Rminus_le_0 ; ring_simplify.
by apply pos_INR.
by left.
ring.
move => k ; rewrite ?S_INR /= ; move: (Haux k) ; rewrite /PS_plus /= /PS_incr_1 /PS_derive_n /PS_scal /PS_derive -?S_INR.
replace (k + 2)%nat with (S (S k)) by ring.
rewrite /fact -/fact ?mult_INR ?S_INR => {Haux} Haux.
rewrite /plus /scal /= /mult /= in Haux.
field_simplify in Haux.
field_simplify.
by rewrite (Rmult_comm (INR n ^ 2)).
move: Haux.
by apply INR_fact_neq_0.
move => k.
apply (PSeries_ext_recip _ (fun _ => 0)).
apply Rbar_lt_le_trans with (2 := CV_radius_plus _ _).
apply Rbar_min_case.
apply Rbar_lt_le_trans with (2 := CV_radius_plus _ _).
apply Rbar_min_case.
rewrite /PS_incr_n ?CV_radius_incr_1.
by rewrite CV_radius_derive_n.
rewrite CV_radius_incr_1.
by rewrite CV_radius_derive.
apply Rbar_lt_le_trans with (2 := CV_radius_plus _ _).
apply Rbar_min_case.
by rewrite /PS_incr_n ?CV_radius_incr_1.
destruct n.
rewrite -(CV_radius_ext (fun _ => 0)) ?CV_radius_const_0.
by [].
intros n ; rewrite /PS_scal /= /scal /= /mult /= ; ring.
rewrite CV_radius_scal ?Ha //.
apply Ropp_neq_0_compat, pow_nonzero, not_0_INR, sym_not_eq, O_S.
by rewrite CV_radius_const_0.
assert (0 < Rbar_min 1 (CV_radius a)).
destruct (CV_radius a) as [ca | | ] ; try by auto.
apply Rbar_min_case => //.
by apply Rlt_0_1.
apply Rbar_min_case_strong => // _.
by apply Rlt_0_1.
exists (mkposreal _ H0) => x Hx.
assert (Rbar_lt (Rabs x) (CV_radius a)).
destruct (CV_radius a) as [ca | | ] ; try by auto.
simpl.
eapply Rlt_le_trans.
rewrite -(Rminus_0_r x).
by apply Hx.
simpl.
apply Rmin_case_strong => // H1.
by apply Req_le.
rewrite PSeries_const_0 ?PSeries_plus.
rewrite ?PSeries_incr_n PSeries_incr_1 PSeries_scal -Derive_n_PSeries.
rewrite -Derive_PSeries.
rewrite -Rmult_plus_distr_r.
apply H.
by apply H1.
by apply H1.
by apply H1.
apply ex_pseries_incr_n, CV_radius_inside, H1.
apply ex_pseries_scal, CV_radius_inside.
by apply Rmult_comm.
by apply H1.
apply ex_pseries_incr_n.
apply CV_radius_inside.
rewrite CV_radius_derive_n.
by apply H1.
apply ex_pseries_incr_1, ex_pseries_derive.
by apply H1.
apply ex_pseries_plus.
apply ex_pseries_incr_n.
apply CV_radius_inside.
by rewrite CV_radius_derive_n ; apply H1.
apply ex_pseries_incr_1, ex_pseries_derive.
by apply H1.
apply ex_pseries_plus.
apply ex_pseries_incr_n.
apply CV_radius_inside.
by apply H1.
apply ex_pseries_scal.
by apply Rmult_comm.
apply CV_radius_inside ; by apply H1.
