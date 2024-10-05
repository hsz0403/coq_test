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

Lemma Lim_exp (x : Rbar) : Lim (fun y => exp y) x = match x with | Finite x => exp x | p_infty => p_infty | m_infty => 0 end.
Proof.
apply is_lim_unique.
case: x => [x | | ].
apply is_lim_continuity.
apply derivable_continuous_pt, derivable_pt_exp.
by apply is_lim_exp_p.
by apply is_lim_exp_m.
