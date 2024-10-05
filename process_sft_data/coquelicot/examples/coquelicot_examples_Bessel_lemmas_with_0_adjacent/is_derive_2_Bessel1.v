Require Import Reals Psatz.
Require Import mathcomp.ssreflect.ssreflect.
Require Import Rcomplements Rbar Hierarchy.
Require Import Derive Series PSeries Lim_seq.
Require Import AutoDerive.
Definition Bessel1_seq (n k : nat) := (-1)^(k)/(INR (fact (k)) * INR (fact (n + (k)))).
Definition Bessel1 (n : nat) (x : R) := (x/2)^n * PSeries (Bessel1_seq n) ((x/2)^2).

Lemma is_derive_2_Bessel1 (n : nat) (x : R) : is_derive_n (Bessel1 n) 2 x (((x/2)^(S (S n)) * PSeries (PS_derive (PS_derive (Bessel1_seq n))) ((x / 2) ^ 2)) + ((INR (2*n+1)/2) * (x/2)^n * PSeries (PS_derive (Bessel1_seq n)) ((x / 2) ^ 2)) + (INR (n * pred n) / 4 * (x / 2) ^ pred (pred n) * PSeries (Bessel1_seq n) ((x / 2) ^ 2))).
Proof.
rewrite plus_INR ?mult_INR ; simpl INR.
eapply is_derive_ext.
move => y ; by apply sym_eq, is_derive_unique, is_derive_Bessel1.
auto_derive.
repeat split.
apply ex_derive_PSeries.
by rewrite CV_radius_derive CV_Bessel1.
apply ex_derive_PSeries.
by rewrite CV_Bessel1.
rewrite !Derive_PSeries.
case: n => [ | n] ; rewrite ?S_INR /Rdiv /= ; field.
by rewrite CV_Bessel1.
by rewrite CV_radius_derive CV_Bessel1.
