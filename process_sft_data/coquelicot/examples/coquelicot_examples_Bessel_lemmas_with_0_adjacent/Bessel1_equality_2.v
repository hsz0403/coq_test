Require Import Reals Psatz.
Require Import mathcomp.ssreflect.ssreflect.
Require Import Rcomplements Rbar Hierarchy.
Require Import Derive Series PSeries Lim_seq.
Require Import AutoDerive.
Definition Bessel1_seq (n k : nat) := (-1)^(k)/(INR (fact (k)) * INR (fact (n + (k)))).
Definition Bessel1 (n : nat) (x : R) := (x/2)^n * PSeries (Bessel1_seq n) ((x/2)^2).

Lemma Bessel1_equality_2 (n : nat) (x : R) : (0 < n)%nat -> x<>0 -> Bessel1 (S n)%nat x + Bessel1 (pred n)%nat x = (2*INR n)/x * Bessel1 n x.
Proof.
case: n => [ | n] Hn Hx.
by apply lt_irrefl in Hn.
clear Hn ; simpl pred.
rewrite /Bessel1 S_INR.
replace ((x / 2) ^ S (S n) * PSeries (Bessel1_seq (S (S n))) ((x / 2) ^ 2) + (x / 2) ^ n * PSeries (Bessel1_seq n) ((x / 2) ^ 2)) with ((x/2)^n * ((x/2)^2 * PSeries (Bessel1_seq (S (S n))) ((x / 2) ^ 2) + PSeries (Bessel1_seq n) ((x / 2) ^ 2))) by (simpl ; ring).
replace (2 * (INR n + 1) / x * ((x / 2) ^ S n * PSeries (Bessel1_seq (S n)) ((x / 2) ^ 2))) with ((x/2)^n * ((INR n + 1) * PSeries (Bessel1_seq (S n)) ((x / 2) ^ 2))) by (simpl ; field ; exact: Hx).
apply f_equal.
rewrite -PSeries_incr_1 -PSeries_scal -PSeries_plus.
Focus 2.
by apply ex_pseries_incr_1, ex_Bessel1.
Focus 2.
by apply ex_Bessel1.
apply PSeries_ext => k.
rewrite /PS_plus /PS_scal /PS_incr_1 /Bessel1_seq ; case: k => [ | k] ; rewrite ?plus_0_r -?plus_n_Sm ?plus_Sn_m /fact -/fact ?mult_INR ?S_INR ?plus_INR /=.
rewrite plus_zero_l /scal /= /mult /=.
field.
rewrite -S_INR ; split ; by [apply not_0_INR, sym_not_eq, O_S | apply INR_fact_neq_0].
rewrite /plus /scal /= /mult /=.
field ; rewrite -?plus_INR -?S_INR ; repeat split ; by [apply INR_fact_neq_0 | apply not_0_INR, sym_not_eq, O_S].
