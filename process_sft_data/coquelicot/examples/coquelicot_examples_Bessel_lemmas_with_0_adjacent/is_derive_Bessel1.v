Require Import Reals Psatz.
Require Import mathcomp.ssreflect.ssreflect.
Require Import Rcomplements Rbar Hierarchy.
Require Import Derive Series PSeries Lim_seq.
Require Import AutoDerive.
Definition Bessel1_seq (n k : nat) := (-1)^(k)/(INR (fact (k)) * INR (fact (n + (k)))).
Definition Bessel1 (n : nat) (x : R) := (x/2)^n * PSeries (Bessel1_seq n) ((x/2)^2).

Lemma is_derive_Bessel1 (n : nat) (x : R) : is_derive (Bessel1 n) x ((x / 2) ^ S n * PSeries (PS_derive (Bessel1_seq n)) ((x / 2) ^ 2) + (INR n)/2 * (x / 2) ^ pred n * PSeries (Bessel1_seq n) ((x / 2) ^ 2)).
Proof.
rewrite /Bessel1.
auto_derive.
apply ex_derive_PSeries.
by rewrite CV_Bessel1.
rewrite Derive_PSeries.
rewrite /Rdiv ; simpl ; field.
by rewrite CV_Bessel1.
