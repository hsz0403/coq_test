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

Lemma ex_series_lim_0 (a : nat -> R) : ex_series a -> is_lim_seq a 0.
Proof.
intros Hs.
apply is_lim_seq_spec.
intros eps.
apply (Cauchy_ex_series (V := R_CompleteNormedModule)) in Hs.
case: (Hs eps) => {Hs} N Hs.
exists (S N) ; case => [ | n] Hn.
by apply le_Sn_0 in Hn.
apply le_S_n in Hn.
replace (a (S n) - 0) with (sum_n_m a (S n) (S n)).
apply Hs ; by intuition.
by rewrite sum_n_n Rminus_0_r.
