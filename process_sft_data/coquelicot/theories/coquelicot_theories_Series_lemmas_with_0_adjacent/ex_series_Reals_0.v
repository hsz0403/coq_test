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

Lemma ex_series_Reals_0 (a : nat -> R) : ex_series a -> { l:R | Un_cv (fun N:nat => sum_f_R0 a N) l }.
Proof.
move => H ; exists (Series a) ; case: H => l H.
replace (Series a) with l.
move => e He ; set eps := mkposreal e He.
apply (is_lim_seq_spec _ l) in H.
case: (H eps) => /= {H} N H.
exists N => n Hn.
rewrite <- sum_n_Reals.
by apply (H n Hn).
apply sym_eq.
rewrite /Series.
replace l with (real (Finite l)) by auto.
apply f_equal.
by apply is_lim_seq_unique.
