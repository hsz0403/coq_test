Require Import Reals Omega Psatz.
Require Import mathcomp.ssreflect.ssreflect.
Require Import Rcomplements.
Require Import Lim_seq Rbar Hierarchy.
Section Definitions.
Context {K : AbsRing} {V : NormedModule K}.
Definition is_series (a : nat -> V) (l : V) := filterlim (sum_n a) (eventually) (locally l).
Definition ex_series (a : nat -> V) := exists l : V, is_series a l.
Definition Cauchy_series (a : nat -> V) := forall eps : posreal, exists N : nat, forall n m : nat, (N <= n)%nat -> (N <= m)%nat -> norm (sum_n_m a n m) < eps.
End Definitions.
Definition Series (a : nat -> R) : R := real (Lim_seq (sum_n a)).
Section Properties1.
Context {K : AbsRing} {V : NormedModule K}.
End Properties1.
Section Properties2.
Context {K : AbsRing} {V : NormedModule K}.
End Properties2.
Section Properties3.
Context {K : AbsRing} {V : NormedModule K}.
End Properties3.

Lemma Cauchy_ex_series {K : AbsRing} {V : CompleteNormedModule K} (a : nat -> V) : ex_series a -> Cauchy_series a.
Proof.
intros [l Hl] eps.
set (eps' := eps / (norm_factor (V := V))).
assert (He: 0 < eps').
apply Rdiv_lt_0_compat.
apply eps.
apply norm_factor_gt_0.
destruct (proj2 (filterlim_locally_cauchy (U := V) (F := eventually) (sum_n (fun k => a k))) (ex_intro _ l Hl) (mkposreal _ He)) as [P [[N HN] HP]].
exists (S N).
intros [|u] v Hu Hv.
elim le_Sn_O with (1 := Hu).
destruct (le_or_lt u v) as [Huv|Huv].
rewrite -> sum_n_m_sum_n with (1 := Huv).
replace (pos eps) with (norm_factor (V := V) * mkposreal _ He).
apply norm_compat2.
apply HP ; apply HN.
now apply le_S_n.
now apply le_Sn_le.
rewrite /eps' /=.
field.
apply Rgt_not_eq, norm_factor_gt_0.
rewrite sum_n_m_zero.
rewrite norm_zero.
apply cond_pos.
now apply lt_S.
