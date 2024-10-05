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

Lemma Series_Rabs (a : nat -> R) : ex_series (fun n => Rabs (a n)) -> Rabs (Series a) <= Series (fun n => Rabs (a n)).
Proof.
move => Hra.
have Ha := (ex_series_Rabs a Hra).
case: Hra => lra Hra.
case: Ha => la Ha.
rewrite /is_series in Hra Ha.
rewrite /Series /=.
replace (Lim_seq (sum_n a)) with (Finite la).
replace (Lim_seq (sum_n (fun k : nat => Rabs (a k)))) with (Finite lra).
simpl.
apply (is_lim_seq_abs _ la) in Ha.
change (Rbar_le (Rabs la) lra).
eapply is_lim_seq_le with (2:=Ha).
2: apply Hra.
elim => [ | n IH] /=.
rewrite !sum_O.
by apply Rle_refl.
rewrite !sum_Sn.
apply Rle_trans with (1 := Rabs_triang _ _).
apply Rplus_le_compat_r.
by apply IH.
by apply sym_eq, is_lim_seq_unique.
by apply sym_eq, is_lim_seq_unique.
