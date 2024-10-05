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

Lemma is_series_decr_n (a : nat -> V) (n : nat) (l : V) : (0 < n)%nat -> is_series (fun k => a (n + k)%nat) (plus l (opp (sum_n a (pred n)))) -> is_series a l.
Proof.
case: n => /= [ | n] Hn Ha.
by apply lt_irrefl in Hn.
clear Hn.
elim: n a l Ha => [ | n IH] a l Ha.
rewrite sum_O in Ha.
by apply is_series_decr_1.
apply is_series_decr_1.
apply IH.
replace (plus (plus l (opp (a 0%nat))) (opp (sum_n (fun k : nat => a (S k)) n))) with (plus l (opp (sum_n a (S n)))).
by apply Ha.
rewrite /sum_n sum_n_m_S sum_Sn_m /=.
rewrite <- plus_assoc.
apply f_equal.
now rewrite opp_plus.
by apply le_O_n.
