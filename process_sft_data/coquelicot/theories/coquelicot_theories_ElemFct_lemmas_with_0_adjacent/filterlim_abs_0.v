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

Lemma filterlim_abs_0 {K : AbsRing} : (forall x : K, abs x = 0 -> x = zero) -> filterlim (abs (K := K)) (locally' (zero (G := K))) (at_right 0).
Proof.
intros H P [eps HP].
exists eps.
intros x Hx Hx'.
apply HP.
revert Hx.
rewrite /ball /= /AbsRing_ball !minus_zero_r {2}/abs /= Rabs_pos_eq.
by [].
by apply abs_ge_0.
assert (abs x <> 0).
contradict Hx' ; by apply H.
case: (abs_ge_0 x) => // H1.
by rewrite -H1 in H0.
