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

Lemma ex_series_Cauchy {K : AbsRing} {V : CompleteNormedModule K} (a : nat -> V) : Cauchy_series a -> ex_series a.
Proof.
intros Ca.
destruct (proj1 (filterlim_locally_cauchy (U := V) (F := eventually) (sum_n a))) as [l Hl].
2: now exists l.
intros eps.
destruct (Ca eps) as [N HN].
exists (le N).
split.
now exists N.
intros u v.
wlog Huv: u v / (u <= v)%nat.
intros H.
destruct (le_or_lt u v) as [Huv|Huv].
now apply H.
intros Hu Hv.
apply ball_sym.
apply H => //.
now apply lt_le_weak.
intros Hu Hv.
apply: norm_compat1.
rewrite <- sum_n_m_sum_n with (1 := Huv).
apply HN => //.
now apply le_S.
