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

Lemma Series_scal_l (c : R) (a : nat -> R) : Series (fun n => c * a n) = c * Series a.
Proof.
rewrite /Series.
have H0 : (forall x, c * Rbar.real x = Rbar.real (Rbar.Rbar_mult (Rbar.Finite c) x)).
case: (Req_dec c 0) => [-> | Hk].
case => [x | | ] //= ; rewrite Rmult_0_l.
case: Rle_dec (Rle_refl 0) => //= H0 _.
case: Rle_lt_or_eq_dec (Rlt_irrefl 0) => //= _ _.
case: Rle_dec (Rle_refl 0) => //= H0 _.
case: Rle_lt_or_eq_dec (Rlt_irrefl 0) => //= _ _.
case => [x | | ] //= ; rewrite Rmult_0_r.
case: Rle_dec => //= H0.
case: Rle_lt_or_eq_dec => //=.
case: Rle_dec => //= H0.
case: Rle_lt_or_eq_dec => //=.
rewrite H0 -(Lim_seq_scal_l _ c).
apply f_equal, Lim_seq_ext.
elim => [ | n IH].
rewrite !sum_O ; ring.
rewrite !sum_Sn IH /plus /=.
ring.
