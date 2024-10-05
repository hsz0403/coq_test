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

Lemma is_lim_sqrt_p (f : R -> R) (x : Rbar) : is_lim f x p_infty -> is_lim (fun x => sqrt (f x)) x p_infty.
Proof.
intros.
eapply filterlim_comp, filterlim_sqrt_p.
by apply H.
