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

Lemma Series_incr_n (a : nat -> R) (n : nat) : (0 < n)%nat -> ex_series a -> Series a = sum_f_R0 a (pred n) + Series (fun k => a (n + k)%nat).
Proof.
move => Hn Ha.
apply is_series_unique.
rewrite Rplus_comm.
apply is_series_decr_n with n.
by [].
rewrite /plus /opp /= sum_n_Reals.
ring_simplify (Series (fun k : nat => a (n+ k)%nat) + sum_f_R0 a (pred n) + - sum_f_R0 a (pred n)).
apply Series_correct.
by apply ex_series_incr_n.
