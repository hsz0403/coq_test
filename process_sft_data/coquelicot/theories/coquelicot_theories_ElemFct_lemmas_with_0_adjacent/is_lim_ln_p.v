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

Lemma is_lim_ln_p : is_lim (fun y => ln y) p_infty p_infty.
Proof.
apply is_lim_spec.
move => M.
exists (exp M) => x Hx.
rewrite -(ln_exp M).
apply ln_increasing.
apply exp_pos.
by apply Hx.
