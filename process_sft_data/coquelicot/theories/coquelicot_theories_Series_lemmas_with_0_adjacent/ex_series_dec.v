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

Lemma ex_series_dec (a : nat -> R) : {ex_series a} + {~ ex_series a}.
Proof.
case: (ex_lim_seq_dec (sum_n a)) => H.
apply Lim_seq_correct in H.
case: (Lim_seq (sum_n a)) H => [l | | ] H.
left ; by exists l.
right ; case => l H0.
absurd (p_infty = Finite l) => //.
rewrite -(is_lim_seq_unique _ _ H).
by apply is_lim_seq_unique.
right ; case => l H0.
absurd (m_infty = Finite l) => //.
rewrite -(is_lim_seq_unique _ _ H).
by apply is_lim_seq_unique.
right ; case => l.
contradict H.
by exists l.
