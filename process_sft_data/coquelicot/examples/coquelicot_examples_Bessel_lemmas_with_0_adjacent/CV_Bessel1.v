Require Import Reals Psatz.
Require Import mathcomp.ssreflect.ssreflect.
Require Import Rcomplements Rbar Hierarchy.
Require Import Derive Series PSeries Lim_seq.
Require Import AutoDerive.
Definition Bessel1_seq (n k : nat) := (-1)^(k)/(INR (fact (k)) * INR (fact (n + (k)))).
Definition Bessel1 (n : nat) (x : R) := (x/2)^n * PSeries (Bessel1_seq n) ((x/2)^2).

Lemma CV_Bessel1 (n : nat) : CV_radius (Bessel1_seq n) = p_infty.
Proof.
apply CV_radius_infinite_DAlembert.
by apply Bessel1_seq_neq_0.
apply is_lim_seq_ext with (fun p => / (INR (S p) * INR (S (n + p)))).
move => p ; rewrite /Bessel1_seq -plus_n_Sm /fact -/fact !mult_INR.
simpl ((-1)^(S p)).
field_simplify (-1 * (-1) ^ p / (INR (S p) * INR (fact p) * (INR (S (n + p)) * INR (fact (n + p)))) / ((-1) ^ p / (INR (fact p) * INR (fact (n + p))))).
rewrite Rabs_div.
rewrite Rabs_Ropp Rabs_R1 /Rdiv Rmult_1_l Rabs_pos_eq.
by [].
apply Rmult_le_pos ; apply pos_INR.
apply Rgt_not_eq, Rmult_lt_0_compat ; apply lt_0_INR, lt_O_Sn.
repeat split.
by apply INR_fact_neq_0.
by apply INR_fact_neq_0.
by apply Rgt_not_eq, lt_0_INR, lt_O_Sn.
by apply Rgt_not_eq, lt_0_INR, lt_O_Sn.
by apply pow_nonzero, Rlt_not_eq, (IZR_lt (-1) 0).
replace (Finite 0) with (Rbar_inv p_infty) by auto.
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
