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

Lemma is_derive_n_pow_bigi: forall i p x, (p < i) %nat -> is_derive_n (fun x : R => x ^ p) i x 0.
Proof.
elim => /= [ | i IH] p x Hip.
by apply lt_n_O in Hip.
apply lt_n_Sm_le, le_lt_eq_dec in Hip.
case: Hip => [Hip | ->] ; eapply is_derive_ext.
intros t ; by apply sym_equal, is_derive_n_unique, IH.
apply @is_derive_const.
intros t ; rewrite Derive_n_pow_smalli.
by rewrite minus_diag /=.
by apply le_refl.
by apply @is_derive_const.
