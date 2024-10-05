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

Lemma is_series_Reals (a : nat -> R) (l : R) : is_series a l <-> infinite_sum a l.
Proof.
split => H.
apply (is_lim_seq_spec _ l) in H.
move => e He ; set eps := mkposreal e He.
case: (H eps) => /= {H} N H.
exists N => n Hn.
rewrite <- sum_n_Reals.
by apply (H n Hn).
apply (is_lim_seq_spec _ l).
move => eps.
case: (H eps (cond_pos eps)) => {H} N H.
exists N => n Hn.
rewrite sum_n_Reals.
by apply (H n Hn).
