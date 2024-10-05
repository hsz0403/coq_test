Require Import Reals Psatz.
Require Import mathcomp.ssreflect.ssreflect.
Require Import Rcomplements Rbar Hierarchy.
Require Import Derive Series PSeries Lim_seq.
Require Import AutoDerive.
Definition Bessel1_seq (n k : nat) := (-1)^(k)/(INR (fact (k)) * INR (fact (n + (k)))).
Definition Bessel1 (n : nat) (x : R) := (x/2)^n * PSeries (Bessel1_seq n) ((x/2)^2).

Lemma Bessel1_seq_neq_0 (n : nat) : forall k, Bessel1_seq n k <> 0.
Proof.
move => k.
apply Rmult_integral_contrapositive_currified.
apply pow_nonzero, Ropp_neq_0_compat, R1_neq_R0.
apply Rinv_neq_0_compat, Rmult_integral_contrapositive_currified ; apply INR_fact_neq_0.
