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

Lemma filterdiff_sqrt (x : R) : 0 < x -> filterdiff sqrt (locally x) (fun y => scal y (/ (2 * sqrt x))).
Proof.
intros Hx.
apply is_derive_Reals.
by apply derivable_pt_lim_sqrt.
