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

Lemma is_derive_sqrt (f : R -> R) (x df : R) : is_derive f x df -> 0 < f x -> is_derive (fun x => sqrt (f x)) x (df / (2 * sqrt (f x))).
Proof.
intros Hf Hfx.
evar_last.
eapply is_derive_comp.
by apply filterdiff_sqrt.
by apply Hf.
reflexivity.
