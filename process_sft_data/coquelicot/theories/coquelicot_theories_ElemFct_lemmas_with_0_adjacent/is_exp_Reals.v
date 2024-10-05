Require Import Reals Omega mathcomp.ssreflect.ssreflect.
Require Import Rbar Rcomplements Continuity Derive Hierarchy RInt PSeries.
Require Import Lim_seq RInt_analysis.
Section nat_to_ring.
Context {K : Ring}.
Definition nat_to_ring (n : nat) : K := sum_n_m (fun _ => one) 1 n.
End nat_to_ring.
Section is_derive_mult.
Context {K : AbsRing}.
End is_derive_mult.

Lemma is_exp_Reals (x : R) : is_pseries (fun n => / INR (fact n)) x (exp x).
Proof.
rewrite /exp.
case: exist_exp => l /= Hl.
apply Series.is_series_Reals in Hl.
move: Hl ; apply Series.is_series_ext => n.
by rewrite Rmult_comm pow_n_pow.
