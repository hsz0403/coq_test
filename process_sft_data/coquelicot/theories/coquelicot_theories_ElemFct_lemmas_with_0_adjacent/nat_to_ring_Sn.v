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

Lemma nat_to_ring_Sn (n : nat) : nat_to_ring (S n) = plus (nat_to_ring n) one.
Proof.
case: n => [ | n] ; rewrite /nat_to_ring.
rewrite sum_n_n sum_n_m_zero //.
by rewrite plus_zero_l.
rewrite sum_n_Sm //.
by apply le_n_S, le_O_n.
