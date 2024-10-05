Require Import Reals Psatz.
Require Import mathcomp.ssreflect.ssreflect.
Require Import Rcomplements Rbar Hierarchy.
Require Import Derive Series PSeries Lim_seq.
Require Import AutoDerive.
Definition Bessel1_seq (n k : nat) := (-1)^(k)/(INR (fact (k)) * INR (fact (n + (k)))).
Definition Bessel1 (n : nat) (x : R) := (x/2)^n * PSeries (Bessel1_seq n) ((x/2)^2).

Lemma Bessel1_equality_1 (n : nat) (x : R) : x <> 0 -> Bessel1 (S n)%nat x = INR n * Bessel1 n x / x - Derive (Bessel1 n) x.
Proof.
move => Hx.
rewrite (is_derive_unique _ _ _ (is_derive_Bessel1 _ _)) /Bessel1.
set y := (x / 2).
replace x with (2 * y) by (unfold y ; field).
have Hy : y <> 0.
unfold y ; contradict Hx.
replace x with (2 * (x/2)) by field ; rewrite Hx ; ring.
case: n => [ | n] ; simpl ; field_simplify => // ; rewrite Rdiv_1 -/(pow _ 2).
replace (- 2 * y ^ 2 * PSeries (PS_derive (Bessel1_seq 0)) (y ^ 2) / (2 * y)) with (y * ((-1) * PSeries (PS_derive (Bessel1_seq 0)) (y ^ 2))) by (simpl ; unfold y ; field => //).
apply f_equal.
rewrite -PSeries_scal.
apply PSeries_ext => k.
rewrite /Bessel1_seq /PS_scal /PS_derive plus_0_l.
replace (1+k)%nat with (S k) by ring.
rewrite /fact -/fact mult_INR /pow -/pow.
change scal with Rmult.
field ; split.
exact: INR_fact_neq_0.
by apply not_0_INR, not_eq_sym, O_S.
replace (-2 * y ^ 2 * y ^ n * PSeries (PS_derive (Bessel1_seq (S n))) (y ^ 2) / 2) with (y^2 * y^n * (((-1)* PSeries (PS_derive (Bessel1_seq (S n))) (y ^ 2)))) by (unfold y ; field => //).
apply f_equal.
rewrite -PSeries_scal.
apply PSeries_ext => k.
rewrite /Bessel1_seq /PS_scal /PS_derive -?plus_n_Sm ?plus_Sn_m.
rewrite /pow -/pow /fact -/fact ?mult_INR ?S_INR plus_INR.
change scal with Rmult.
field.
rewrite -plus_INR -?S_INR.
repeat split ; try by [exact: INR_fact_neq_0 | apply not_0_INR, not_eq_sym, O_S].
