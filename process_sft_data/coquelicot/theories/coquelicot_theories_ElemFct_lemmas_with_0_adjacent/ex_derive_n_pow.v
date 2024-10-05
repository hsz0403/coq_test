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

Lemma ex_derive_n_pow i p x: ex_derive_n (fun x : R => x ^ p) i x.
Proof.
case: i => //= i.
exists (Derive_n (fun x : R => x ^ p) (S i) x).
rewrite Derive_n_pow.
case: le_dec => Hip.
by apply (is_derive_n_pow_smalli (S i)).
apply (is_derive_n_pow_bigi (S i)) ; omega.
