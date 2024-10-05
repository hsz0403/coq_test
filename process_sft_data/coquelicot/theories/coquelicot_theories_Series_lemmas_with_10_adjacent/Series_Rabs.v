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
Admitted.

Lemma ex_series_incr_1 (a : nat -> V) : ex_series a <-> ex_series (fun k => a (S k)%nat).
Proof.
split ; move => [la Ha].
exists (plus la (opp (a O))).
apply is_series_incr_1.
now rewrite <- plus_assoc, plus_opp_l, plus_zero_r.
exists (plus la (a O)).
apply is_series_decr_1.
Admitted.

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
Admitted.

Lemma Series_incr_1 (a : nat -> R) : ex_series a -> Series a = a O + Series (fun k => a (S k)).
Proof.
move => Ha.
apply is_series_unique.
rewrite Rplus_comm.
apply is_series_decr_1.
rewrite /plus /opp /=.
ring_simplify (Series (fun k : nat => a (S k)) + a 0%nat +- a 0%nat).
apply Series_correct.
Admitted.

Lemma Series_incr_n (a : nat -> R) (n : nat) : (0 < n)%nat -> ex_series a -> Series a = sum_f_R0 a (pred n) + Series (fun k => a (n + k)%nat).
Proof.
move => Hn Ha.
apply is_series_unique.
rewrite Rplus_comm.
apply is_series_decr_n with n.
by [].
rewrite /plus /opp /= sum_n_Reals.
ring_simplify (Series (fun k : nat => a (n+ k)%nat) + sum_f_R0 a (pred n) + - sum_f_R0 a (pred n)).
apply Series_correct.
Admitted.

Lemma Series_incr_1_aux (a : nat -> R) : a O = 0 -> Series a = Series (fun k => a (S k)).
Proof.
move => Ha.
rewrite /Series.
rewrite -Lim_seq_incr_1.
apply f_equal, Lim_seq_ext => n.
rewrite /sum_n sum_n_m_S sum_Sn_m.
rewrite Ha ; by apply Rplus_0_l.
Admitted.

Lemma Series_incr_n_aux (a : nat -> R) (n : nat) : (forall k, (k < n)%nat -> a k = 0) -> Series a = Series (fun k => a (n + k)%nat).
Proof.
elim: n => [ | n IH] Ha.
by apply Series_ext => k.
rewrite IH.
rewrite Series_incr_1_aux.
apply Series_ext => k.
apply f_equal ; ring.
intuition.
Admitted.

Lemma Cauchy_series_Reals (a : nat -> R) : Cauchy_series a <-> Cauchy_crit_series a.
Proof.
split => Hcv.
apply cv_cauchy_1, ex_series_Reals_0.
by apply: ex_series_Cauchy.
apply: Cauchy_ex_series.
apply ex_series_Reals_1.
apply cv_cauchy_2.
Admitted.

Lemma ex_series_lim_0 (a : nat -> R) : ex_series a -> is_lim_seq a 0.
Proof.
intros Hs.
apply is_lim_seq_spec.
intros eps.
apply (Cauchy_ex_series (V := R_CompleteNormedModule)) in Hs.
case: (Hs eps) => {Hs} N Hs.
exists (S N) ; case => [ | n] Hn.
by apply le_Sn_0 in Hn.
apply le_S_n in Hn.
replace (a (S n) - 0) with (sum_n_m a (S n) (S n)).
apply Hs ; by intuition.
Admitted.

Lemma ex_series_Rabs (a : nat -> R) : ex_series (fun n => Rabs (a n)) -> ex_series a.
Proof.
move => H.
apply: ex_series_Cauchy.
apply Cauchy_series_Reals.
apply cauchy_abs.
apply Cauchy_series_Reals.
Admitted.

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
Admitted.

Lemma Series_le (a b : nat -> R) : (forall n : nat, 0 <= a n <= b n) -> ex_series b -> Series a <= Series b.
Proof.
move => Hn Hb.
have Ha := (ex_series_le a b).
apply Lim_seq_correct' in Ha.
apply Lim_seq_correct' in Hb.
move: Ha Hb ; apply is_lim_seq_le.
elim => [ | n IH] /=.
rewrite !sum_O.
by apply Hn.
rewrite !sum_Sn.
apply Rplus_le_compat.
by apply IH.
by apply Hn.
intros n.
rewrite /norm /= /abs /= Rabs_pos_eq ; by apply Hn.
Admitted.

Lemma is_series_opp (a : nat -> V) (la : V) : is_series a la -> is_series (fun n => opp (a n)) (opp la).
Proof.
move => Ha.
apply filterlim_ext with (fun n => opp (sum_n a n)).
elim => [ | n IH].
rewrite !sum_O ; easy.
rewrite !sum_Sn -IH.
apply opp_plus.
apply filterlim_comp with (1:=Ha).
Admitted.

Lemma ex_series_opp (a : nat -> V) : ex_series a -> ex_series (fun n => opp (a n)).
Proof.
move => [la Ha].
exists (opp la).
Admitted.

Lemma Series_opp (a : nat -> R) : Series (fun n => - a n) = - Series a.
Proof.
rewrite /Series (Lim_seq_ext (sum_n (fun k : nat => - a k)) (fun n => - (sum_n (fun k => a k) n))).
rewrite Lim_seq_opp.
by rewrite Rbar_opp_real.
elim => [ | n IH].
rewrite !sum_O ; ring.
rewrite !sum_Sn IH /plus /=.
Admitted.

Lemma is_series_plus (a b : nat -> V) (la lb : V) : is_series a la -> is_series b lb -> is_series (fun n => plus (a n) (b n)) (plus la lb).
Proof.
move => Ha Hb.
apply filterlim_ext with (fun n => plus (sum_n a n) (sum_n b n)).
elim => [ | n IH]; simpl.
by rewrite !sum_O.
rewrite !sum_Sn -IH; rewrite <- 2!plus_assoc; apply f_equal.
rewrite 2!plus_assoc; apply f_equal2; try easy.
apply plus_comm.
Admitted.

Lemma ex_series_plus (a b : nat -> V) : ex_series a -> ex_series b -> ex_series (fun n => plus (a n) (b n)).
Proof.
move => [la Ha] [lb Hb].
exists (plus la lb).
Admitted.

Lemma is_series_minus (a b : nat -> V) (la lb : V) : is_series a la -> is_series b lb -> is_series (fun n => plus (a n) (opp (b n))) (plus la (opp lb)).
Proof.
move => Ha Hb.
apply is_series_plus => //.
Admitted.

Lemma ex_series_minus (a b : nat -> V) : ex_series a -> ex_series b -> ex_series (fun n => plus (a n) (opp (b n))).
Proof.
move => Ha Hb.
apply ex_series_plus => //.
Admitted.

Lemma Series_plus (a b : nat -> R) : ex_series a -> ex_series b -> Series (fun n => a n + b n) = Series a + Series b.
Proof.
intros Ha Hb.
replace (Series a + Series b) with (real (Series a + Series b)) by auto.
apply (f_equal real), is_lim_seq_unique.
Admitted.

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
