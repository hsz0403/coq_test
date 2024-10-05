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

Lemma ex_series_le {K : AbsRing} {V : CompleteNormedModule K} (a : nat -> V) (b : nat -> R) : (forall n : nat, norm (a n) <= b n) -> ex_series b -> ex_series a.
Proof.
move => H Hb.
apply (Cauchy_ex_series (V := R_CompleteNormedModule)) in Hb.
apply ex_series_Cauchy.
move => e.
case (Hb e) => {Hb} N Hb.
exists N => n m Hn Hm.
eapply Rle_lt_trans, (Hb _ _ Hn Hm) => //.
eapply Rle_trans.
apply norm_sum_n_m.
apply Rle_trans with (sum_n_m b n m).
by apply sum_n_m_le.
right.
assert (forall n, 0 <= b n).
intros k.
eapply Rle_trans, H.
by apply norm_ge_0.
clear -H0.
apply sym_eq, Rabs_pos_eq.
elim: n m b H0 => /= [ | n IH] m b Hb.
elim: m => /= [ | m IH].
rewrite sum_n_n.
by apply Hb.
rewrite sum_n_Sm.
by apply Rplus_le_le_0_compat.
by apply le_O_n.
case: m => /= [ | m].
by apply Rle_refl.
rewrite -sum_n_m_S.
apply IH => k.
by apply Hb.
