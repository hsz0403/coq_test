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

Lemma is_derive_Rabs (f : R -> R) (x df : R) : is_derive f x df -> f x <> 0 -> is_derive (fun x => Rabs (f x)) x (sign (f x) * df).
Proof.
intros Hf Hfx.
evar_last.
apply is_derive_comp, Hf.
by apply filterdiff_Rabs.
apply Rmult_comm.
