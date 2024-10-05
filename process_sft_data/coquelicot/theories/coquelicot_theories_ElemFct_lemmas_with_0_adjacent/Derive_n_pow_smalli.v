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

Lemma Derive_n_pow_smalli: forall i p x, (i <= p)%nat -> Derive_n (fun x : R => x ^ p) i x = INR (fact p) / INR (fact (p - i)%nat) * x ^ (p - i)%nat.
Proof.
intros.
now apply is_derive_n_unique, is_derive_n_pow_smalli.
