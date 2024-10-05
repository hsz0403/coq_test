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

Lemma is_lim_Rabs_0 (f : R -> R) (x : Rbar) : is_lim f x 0 -> Rbar_locally' x (fun x => f x <> 0) -> filterlim (fun x => Rabs (f x)) (Rbar_locally' x) (at_right 0).
Proof.
intros.
eapply filterlim_comp, filterlim_Rabs_0.
intros P HP.
apply H in HP.
generalize (filter_and _ _ H0 HP).
rewrite /filtermap /= ; apply filter_imp.
intros y Hy.
apply Hy, Hy.
