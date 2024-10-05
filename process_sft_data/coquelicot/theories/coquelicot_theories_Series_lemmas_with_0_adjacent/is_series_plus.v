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

Lemma is_series_plus (a b : nat -> V) (la lb : V) : is_series a la -> is_series b lb -> is_series (fun n => plus (a n) (b n)) (plus la lb).
Proof.
move => Ha Hb.
apply filterlim_ext with (fun n => plus (sum_n a n) (sum_n b n)).
elim => [ | n IH]; simpl.
by rewrite !sum_O.
rewrite !sum_Sn -IH; rewrite <- 2!plus_assoc; apply f_equal.
rewrite 2!plus_assoc; apply f_equal2; try easy.
apply plus_comm.
now apply filterlim_comp_2 with (3 := filterlim_plus _ _).
