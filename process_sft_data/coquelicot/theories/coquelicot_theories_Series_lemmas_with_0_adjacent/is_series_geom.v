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

Lemma is_series_geom (q : R) : Rabs q < 1 -> is_series (fun n => q ^ n) (/ (1-q)).
Proof.
move => Hq.
apply filterlim_ext with (fun n => (1-q^(S n)) / (1-q)).
move => n.
rewrite sum_n_Reals; rewrite tech3.
reflexivity.
apply Rlt_not_eq.
apply Rle_lt_trans with (2 := Hq).
apply Rle_abs.
change (is_lim_seq (fun n : nat => (1 - q ^ S n) / (1 - q)) (/(1-q))).
replace ((/ (1 - q))) with (real (Rbar_mult (Rbar_minus 1 0) (/ (1 - q)))).
unfold Rdiv.
apply (is_lim_seq_scal_r (fun n : nat => (1 - q ^ S n)) (/ (1 - q)) (Rbar_minus 1 0)).
apply is_lim_seq_minus'.
by apply is_lim_seq_const.
apply (is_lim_seq_incr_1 (fun n => q^n)).
by apply is_lim_seq_geom.
simpl; ring.
