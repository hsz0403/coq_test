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

Lemma is_RInt_exp : forall a b, is_RInt exp a b (exp b - exp a).
Proof.
intros a b.
apply: is_RInt_derive.
intros x _.
apply is_derive_Reals, derivable_pt_lim_exp.
intros x _.
apply continuity_pt_filterlim.
apply derivable_continuous_pt.
apply derivable_pt_exp.
