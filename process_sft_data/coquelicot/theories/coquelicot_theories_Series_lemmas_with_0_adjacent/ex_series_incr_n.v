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

Lemma ex_series_incr_n (a : nat -> V) (n : nat) : ex_series a <-> ex_series (fun k => a (n + k)%nat).
Proof.
case: n => [ | n].
split ; apply ex_series_ext ; by intuition.
split ; move => [la Ha].
exists (plus la (opp (sum_n a (pred (S n))))).
apply is_series_incr_n.
by apply lt_O_Sn.
now rewrite <- plus_assoc, plus_opp_l, plus_zero_r.
exists (plus la (sum_n a (pred (S n)))).
apply is_series_decr_n with (S n).
by apply lt_O_Sn.
now rewrite <- plus_assoc, plus_opp_r, plus_zero_r.
