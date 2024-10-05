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

Lemma is_lim_div_expm1_0 : is_lim (fun y => (exp y - 1) / y) 0 1.
Proof.
apply is_lim_spec.
move => eps.
case: (derivable_pt_lim_exp_0 eps (cond_pos eps)) => delta H.
exists delta => y Hy Hy0.
rewrite /ball /= /AbsRing_ball /= /minus /plus /opp /= in Hy.
rewrite -/(Rminus _ _) Rminus_0_r in Hy.
move: (H y Hy0 Hy).
by rewrite Rplus_0_l exp_0.
