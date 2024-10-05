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

Lemma ex_lim_exp (x : Rbar) : ex_lim (fun y => exp y) x.
Proof.
case: x => [x | | ].
apply ex_finite_lim_correct, ex_lim_continuity.
apply derivable_continuous_pt, derivable_pt_exp.
exists p_infty ; by apply is_lim_exp_p.
exists 0 ; by apply is_lim_exp_m.
