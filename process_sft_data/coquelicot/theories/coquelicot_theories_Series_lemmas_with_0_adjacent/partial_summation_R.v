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

Lemma partial_summation_R (a b : nat -> R) : (exists M, forall n, norm (sum_n b n) <= M) -> filterlim a eventually (locally 0) -> ex_series (fun n => norm (minus (a (S n)) (a n))) -> ex_series (fun n => scal (a n) (b n)).
Proof.
set B := fun n => sum_n b n.
intros Hb Ha0 Ha.
eexists.
unfold is_series.
replace (@locally R_NormedModule) with (fun x => Rbar_locally (Finite x)) by auto.
apply is_lim_seq_ext with (fun N => plus (scal (a N) (B N)) (match N with | O => zero | S N => sum_n (fun n => scal (minus (a n) (a (S n))) (B n)) N end)).
case => /= [ | N].
rewrite /B /= !sum_O ; by apply plus_zero_r.
rewrite sum_Sn plus_comm.
elim: N => /= [ | N IH].
rewrite /B /= !sum_Sn !sum_O /minus !scal_distr_r !scal_distr_l !scal_opp_l.
rewrite -!plus_assoc.
apply f_equal.
rewrite plus_comm -!plus_assoc.
rewrite plus_comm -!plus_assoc.
rewrite plus_opp_l.
by apply plus_zero_r.
rewrite !sum_Sn -IH ; clear IH.
rewrite /B /= /minus !sum_Sn.
generalize (sum_n (fun n : nat => scal (plus (a n) (opp (a (S n)))) (sum_n b n)) N) => /= c.
generalize (sum_n b N) => b'.
rewrite !scal_distr_r !scal_distr_l -!plus_assoc !scal_opp_l.
repeat apply f_equal.
repeat rewrite (plus_comm (scal (a (S (S N))) b')) -!plus_assoc.
rewrite plus_comm -!plus_assoc plus_opp_r plus_zero_r.
by rewrite plus_assoc plus_opp_l plus_zero_l.
apply is_lim_seq_plus'.
instantiate (1 := 0).
apply filterlim_locally => eps.
destruct Hb as [M Hb].
eapply filter_imp.
intros n Hn.
apply @norm_compat1.
rewrite /minus opp_zero plus_zero_r.
eapply Rle_lt_trans.
apply @norm_scal.
eapply Rle_lt_trans.
apply Rmult_le_compat_l.
by apply abs_ge_0.
eapply Rle_trans.
by apply Hb.
apply (Rmax_r 1).
apply Rlt_div_r.
eapply Rlt_le_trans, Rmax_l.
by apply Rlt_0_1.
apply Hn.
assert (0 < eps / Rmax 1 M).
apply Rdiv_lt_0_compat.
by apply eps.
eapply Rlt_le_trans, Rmax_l.
by apply Rlt_0_1.
destruct (proj1 (filterlim_locally _ _) Ha0 (mkposreal _ H)) as [N HN].
exists N => n Hn.
eapply Rle_lt_trans, HN, Hn.
rewrite /minus opp_zero plus_zero_r.
by apply Rle_refl.
apply is_lim_seq_incr_1.
apply (Lim_seq_correct' (fun n : nat => sum_n (fun n0 : nat => scal (minus (a n0) (a (S n0))) (B n0)) n)).
case: Hb => M Hb.
eapply @ex_series_le.
intros n.
eapply Rle_trans.
apply @norm_scal.
apply Rmult_le_compat_l.
by apply abs_ge_0.
by apply Hb.
apply ex_series_scal_r.
move: Ha ; apply ex_series_ext => n.
by rewrite -norm_opp /minus opp_plus opp_opp plus_comm.
