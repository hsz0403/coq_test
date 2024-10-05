Require Import Reals Psatz.
Require Import mathcomp.ssreflect.ssreflect.
Require Import Rcomplements Rbar Hierarchy.
Require Import Derive Series PSeries Lim_seq.
Require Import AutoDerive.
Definition Bessel1_seq (n k : nat) := (-1)^(k)/(INR (fact (k)) * INR (fact (n + (k)))).
Definition Bessel1 (n : nat) (x : R) := (x/2)^n * PSeries (Bessel1_seq n) ((x/2)^2).

Lemma Bessel1_equality_3 (n : nat) (x : R) : (0 < n)%nat -> Bessel1 (S n)%nat x - Bessel1 (pred n)%nat x = - 2 * Derive (Bessel1 n) x.
Proof.
move => Hn.
rewrite (is_derive_unique _ _ _ (is_derive_Bessel1 _ _)) /Bessel1.
case: n Hn => [ | n] Hn.
by apply lt_irrefl in Hn.
clear Hn ; simpl pred.
replace ((x / 2) ^ S (S n) * PSeries (Bessel1_seq (S (S n))) ((x / 2) ^ 2) - (x / 2) ^ n * PSeries (Bessel1_seq n) ((x / 2) ^ 2)) with ((x/2)^n * ((x/2)^2 * PSeries (Bessel1_seq (S (S n))) ((x / 2) ^ 2) - PSeries (Bessel1_seq n) ((x / 2) ^ 2))) by (simpl ; ring).
replace (-2 *((x / 2) ^ S (S n) * PSeries (PS_derive (Bessel1_seq (S n))) ((x / 2) ^ 2) + INR (S n) / 2 * (x / 2) ^ n * PSeries (Bessel1_seq (S n)) ((x / 2) ^ 2))) with ((x/2)^n * (-2 * ((x/2)^2 * PSeries (PS_derive (Bessel1_seq (S n))) ((x / 2) ^ 2)) - INR (S n) * PSeries (Bessel1_seq (S n)) ((x / 2) ^ 2))) by (rewrite S_INR ; simpl ; field).
set y := (x / 2).
apply f_equal.
rewrite -?PSeries_incr_1 -?PSeries_scal -?PSeries_minus.
apply PSeries_ext => k.
rewrite /PS_minus /PS_incr_1 /PS_scal /PS_derive /Bessel1_seq.
case: k => [ | k] ; rewrite -?plus_n_Sm ?plus_Sn_m /fact -/fact ?mult_INR ?S_INR -?plus_n_O ?plus_INR /= ; rewrite /plus /opp /zero /scal /= /mult /= ; field ; rewrite -?plus_INR -?S_INR.
split ; (apply INR_fact_neq_0 || apply not_0_INR, sym_not_eq, O_S).
repeat split ; (apply INR_fact_neq_0 || apply not_0_INR, sym_not_eq, O_S).
apply @ex_pseries_scal, @ex_pseries_incr_1, ex_pseries_derive.
by apply Rmult_comm.
by rewrite CV_Bessel1.
apply ex_pseries_scal, ex_Bessel1.
by apply Rmult_comm.
by apply ex_pseries_incr_1, ex_Bessel1.
by apply ex_Bessel1.
