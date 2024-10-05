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

Lemma filterlim_sqrt_p : filterlim sqrt (Rbar_locally' p_infty) (Rbar_locally p_infty).
Proof.
apply is_lim_spec.
move => M.
exists ((Rmax 0 M)²) => x Hx.
apply Rle_lt_trans with (1 := Rmax_r 0 M).
rewrite -(sqrt_Rsqr (Rmax 0 M)).
apply sqrt_lt_1_alt.
split.
apply Rle_0_sqr.
by apply Hx.
apply Rmax_l.
