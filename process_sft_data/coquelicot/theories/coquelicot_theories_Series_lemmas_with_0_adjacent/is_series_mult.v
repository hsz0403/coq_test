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

Lemma is_series_mult (a b : nat -> R) (la lb : R) : is_series a la -> is_series b lb -> ex_series (fun n => Rabs (a n)) -> ex_series (fun n => Rabs (b n)) -> is_series (fun n => sum_f_R0 (fun k => a k * b (n - k)%nat) n) (la * lb).
Proof.
move => Hla Hlb Ha Hb.
set ap := fun n => (a n + Rabs (a n)) / 2.
set am := fun n => - (a n - Rabs (a n)) / 2.
set bp := fun n => (b n + Rabs (b n)) / 2.
set bm := fun n => - (b n - Rabs (b n)) / 2.
have Hap : forall n, 0 <= ap n.
move => n ; apply Rdiv_le_0_compat.
rewrite Rplus_comm ; apply Rle_minus_l ; rewrite Rminus_0_l.
apply Rabs_maj2.
by apply Rlt_0_2.
assert (Sap : ex_series ap).
apply ex_series_scal_r.
apply (@ex_series_plus ) => //.
by exists la.
have Ham : forall n, 0 <= am n.
move => n ; apply Rdiv_le_0_compat.
rewrite Ropp_minus_distr'.
apply (Rminus_le_0 (a _)).
by apply Rle_abs.
by apply Rlt_0_2.
assert (Sam : ex_series am).
apply ex_series_scal_r.
apply @ex_series_opp.
apply @ex_series_minus => //.
by exists la.
have Hbp : forall n, 0 <= bp n.
move => n ; apply Rdiv_le_0_compat.
rewrite Rplus_comm ; apply Rle_minus_l ; rewrite Rminus_0_l.
apply Rabs_maj2.
by apply Rlt_0_2.
assert (Sbp : ex_series bp).
apply ex_series_scal_r.
apply @ex_series_plus => //.
by exists lb.
have Hbm : forall n, 0 <= bm n.
move => n ; apply Rdiv_le_0_compat.
rewrite Ropp_minus_distr'.
apply (Rminus_le_0 (b _)).
by apply Rle_abs.
by apply Rlt_0_2.
assert (Sbm : ex_series bm).
apply ex_series_scal_r.
apply @ex_series_opp.
apply @ex_series_minus => //.
by exists lb.
apply is_series_ext with (fun n => sum_f_R0 (fun k : nat => ap k * bp (n - k)%nat) n - sum_f_R0 (fun k : nat => am k * bp (n - k)%nat) n - sum_f_R0 (fun k : nat => ap k * bm (n - k)%nat) n + sum_f_R0 (fun k : nat => am k * bm (n - k)%nat) n).
move => n.
rewrite -?minus_sum -plus_sum.
apply sum_eq => k _.
rewrite /ap /am /bp /bm ; field.
replace (la*lb) with ((Series ap*Series bp-Series am*Series bp-Series ap*Series bm)+Series am*Series bm).
apply @is_series_plus.
apply @is_series_minus.
apply @is_series_minus.
apply is_series_mult_pos => // ; by apply Series_correct.
apply is_series_mult_pos => // ; by apply Series_correct.
apply is_series_mult_pos => // ; by apply Series_correct.
apply is_series_mult_pos => // ; by apply Series_correct.
replace (la) with (Series ap - Series am).
replace (lb) with (Series bp - Series bm).
ring.
rewrite -Series_minus // -(is_series_unique _ _ Hlb) ; apply Series_ext => n.
rewrite /ap /am /bp /bm ; field.
rewrite -Series_minus // -(is_series_unique _ _ Hla) ; apply Series_ext => n.
rewrite /ap /am /bp /bm ; field.
