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

Lemma is_series_scal (c : K) (a : nat -> V) (l : V) : is_series a l -> is_series (fun n => scal c (a n)) (scal c l).
Proof.
move => Ha.
apply filterlim_ext with (fun n => scal c (sum_n a n)).
elim => [ | n IH]; simpl.
by rewrite !sum_O.
rewrite !sum_Sn -IH.
apply: scal_distr_l.
Admitted.

Lemma is_series_scal_l : forall (c : K) (a : nat -> V) (l : V), is_series a l -> is_series (fun n => scal c (a n)) (scal c l).
Admitted.

Lemma ex_series_scal (c : K) (a : nat -> V) : ex_series a -> ex_series (fun n => scal c (a n)).
Proof.
move => [l Ha].
exists (scal c l).
Admitted.

Lemma ex_series_scal_l : forall (c : K) (a : nat -> V), ex_series a -> ex_series (fun n => scal c (a n)).
Admitted.

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
Admitted.

Lemma is_series_scal_r (c : R) (a : nat -> R) (l : R) : is_series a l -> is_series (fun n => (a n) * c) (l * c).
Proof.
move => Ha.
rewrite Rmult_comm.
apply is_series_ext with (fun n : nat => c * a n).
move => n ; apply Rmult_comm.
Admitted.

Lemma ex_series_scal_r (c : R) (a : nat -> R) : ex_series a -> ex_series (fun n => a n * c).
Proof.
intros [l Ha].
exists (l * c).
Admitted.

Lemma Series_scal_r (c : R) (a : nat -> R) : Series (fun n => a n * c) = Series a * c.
Proof.
rewrite Rmult_comm -Series_scal_l.
apply Series_ext.
Admitted.

Lemma is_series_mult_pos (a b : nat -> R) (la lb : R) : is_series a la -> is_series b lb -> (forall n, 0 <= a n) -> (forall n, 0 <= b n) -> is_series (fun n => sum_f_R0 (fun k => a k * b (n - k)%nat) n) (la * lb).
Proof.
move => Hla Hlb Ha Hb.
have H0 : forall n, sum_f_R0 (fun k : nat => sum_f_R0 (fun p : nat => a p * b (k - p)%nat) k) n <= sum_f_R0 a n * sum_f_R0 b n.
case => [ | n].
simpl ; apply Rle_refl.
rewrite (cauchy_finite a b (S n) (lt_O_Sn n)).
apply Rminus_le_0 ; ring_simplify.
apply cond_pos_sum => m.
apply cond_pos_sum => k.
by apply Rmult_le_pos.
have H1 : forall n, sum_f_R0 a n * sum_f_R0 b n <= sum_f_R0 (fun k : nat => sum_f_R0 (fun p : nat => a p * b (k - p)%nat) k) ((2*n)%nat).
case => [ /= | n].
by apply Rle_refl.
rewrite (cauchy_finite a b (S n) (lt_O_Sn n)).
rewrite Rplus_comm ; apply Rle_minus_r.
replace (pred (S n)) with n by auto.
replace (2 * S n)%nat with (S n + S n)%nat by ring.
rewrite -sum_f_rw.
rewrite /sum_f.
replace (S n + S n - S (S n))%nat with n.
elim: {1 5 8}n (le_refl n) => [ | m IH] Hm ; rewrite /sum_f_R0 -/sum_f_R0.
rewrite -minus_n_O plus_0_l ; simpl pred.
rewrite -?sum_f_rw_0.
replace (sum_f 0 (S (S n)) (fun p : nat => a p * b (S (S n) - p)%nat)) with ((sum_f 0 (S (S n)) (fun p : nat => a p * b (S (S n) - p)%nat) - (fun p : nat => a p * b (S (S n) - p)%nat) 0%nat) + a O * b (S (S n))) by (rewrite -minus_n_O ; ring).
rewrite -(sum_f_Sn_m _ O (S (S n))) ; [ | by apply lt_O_Sn].
rewrite sum_f_u_Sk ; [ | by apply le_O_n].
rewrite sum_f_n_Sm ; [ | by apply le_O_n].
apply Rle_trans with (sum_f 0 n (fun l0 : nat => a (S (l0 + 0)) * b (S n - l0)%nat) + a (S (S n)) * b (S (S n) - S (S n))%nat + a 0%nat * b (S (S n))).
apply Rminus_le_0 ; ring_simplify.
apply Rplus_le_le_0_compat ; by apply Rmult_le_pos.
repeat apply Rplus_le_compat_r.
apply Req_le.
rewrite ?sum_f_rw_0.
elim: {1 4 6}n (le_refl n) => [ | k IH] Hk // ; rewrite /sum_f_R0 -/sum_f_R0.
rewrite IH ; try by intuition.
apply f_equal.
by rewrite plus_0_r /=.
apply Rplus_le_compat.
apply IH ; intuition.
rewrite -?sum_f_rw_0.
rewrite MyNat.sub_succ_l ; try by intuition.
replace (pred (S (n - S m))) with (n - S m)%nat by auto.
rewrite plus_Sn_m -?plus_n_Sm.
replace (sum_f 0 (S (S (S (m + n)))) (fun p : nat => a p * b (S (S (S (m + n))) - p)%nat)) with (sum_f 1 (S (S (S (m + n)))) (fun p : nat => a p * b (S (S (S (m + n))) - p)%nat) + a O * b (S (S (S (m + n))))).
rewrite -(Rplus_0_r (sum_f O _ _)).
apply Rplus_le_compat.
rewrite (sum_f_chasles _ O (S m) (S (S (S (m + n))))) ; try by intuition.
rewrite -(Rplus_0_l (sum_f O _ _)).
apply Rplus_le_compat.
rewrite /sum_f.
elim: (S m - 1)%nat => {IH} [ | k IH] ; rewrite /sum_f_R0 -/sum_f_R0 //.
by apply Rmult_le_pos.
apply Rplus_le_le_0_compat.
by apply IH.
by apply Rmult_le_pos.
replace (S (S m)) with (1 + S m)%nat by ring.
replace (S (S (S (m + n)))) with (S (S n) + S m )%nat by ring.
rewrite sum_f_u_add.
rewrite (sum_f_chasles _ O (S (n - S m)) (S (S n))) ; try by intuition.
rewrite -(Rplus_0_r (sum_f O _ _)).
apply Rplus_le_compat.
rewrite sum_f_u_Sk.
rewrite ?sum_f_rw_0.
apply Req_le.
elim: (n - S m)%nat => {IH} [ | k IH] ; rewrite /sum_f_R0 -/sum_f_R0 //.
apply f_equal2 ; apply f_equal ; intuition.
rewrite IH ; apply f_equal, f_equal2 ; apply f_equal.
ring.
rewrite ?(Coq.Arith.Plus.plus_comm _ (S m)) -minus_plus_simpl_l_reverse //=.
apply le_O_n.
rewrite /sum_f.
elim: (S (S n) - S (S (n - S m)))%nat => {IH} [ | k IH] ; rewrite /sum_f_R0 -/sum_f_R0 //.
by apply Rmult_le_pos.
apply Rplus_le_le_0_compat => // ; by apply Rmult_le_pos.
by apply le_n_S, le_O_n.
by apply Rmult_le_pos.
rewrite sum_f_Sn_m -?minus_n_O ; try by intuition.
ring.
replace (S (S n)) with (S n + 1)%nat.
rewrite -minus_plus_simpl_l_reverse.
simpl; apply minus_n_O.
now rewrite Coq.Arith.Plus.plus_comm.
elim: n => [ | n IH] //.
rewrite -plus_n_Sm plus_Sn_m.
apply lt_n_S ; intuition.
have H2 : forall n, sum_f_R0 a (Div2.div2 n)%nat * sum_f_R0 b (Div2.div2 n)%nat <= sum_f_R0 (fun k : nat => sum_f_R0 (fun p : nat => a p * b (k - p)%nat) k) n.
move => n.
case: (even_odd_cor n) => k ; case => -> {n}.
rewrite div2_double.
by apply H1.
rewrite div2_S_double.
apply Rle_trans with (1 := H1 _).
apply Rminus_le_0 ; rewrite -sum_f_rw ; try by intuition.
rewrite /sum_f minus_diag /sum_f_R0 -/sum_f_R0.
apply cond_pos_sum => l ; by apply Rmult_le_pos.
change (is_lim_seq (sum_n (fun n : nat => sum_f_R0 (fun k : nat => a k * b (n - k)%nat) n)) (Finite (la * lb))).
apply is_lim_seq_le_le with (u := fun n => sum_f_R0 a (Div2.div2 n) * sum_f_R0 b (Div2.div2 n)) (w := fun n => sum_f_R0 a n * sum_f_R0 b n).
intros n; rewrite sum_n_Reals.
by split.
replace (Finite (la * lb)) with (Rbar_mult la lb) by auto.
suff H : is_lim_seq (fun n : nat => sum_f_R0 a n * sum_f_R0 b n) (Rbar_mult la lb).
apply is_lim_seq_spec in H.
apply is_lim_seq_spec.
move => eps.
case: (H eps) => {H} N H.
exists (S (2 * N))%nat => n Hn.
apply H.
apply le_double.
apply le_S_n.
apply le_trans with (1 := Hn).
apply (Div2.ind_0_1_SS (fun n => (n <= S (2 * Div2.div2 n))%nat)).
by apply le_O_n.
by apply le_refl.
move => k Hk.
replace (Div2.div2 (S (S k))) with (S (Div2.div2 k)) by auto.
replace (2 * S (Div2.div2 k))%nat with (S (S (2 * Div2.div2 k))) by ring.
by repeat apply le_n_S.
apply is_lim_seq_mult'.
apply filterlim_ext with (2:=Hla); apply sum_n_Reals.
apply filterlim_ext with (2:=Hlb); apply sum_n_Reals.
apply is_lim_seq_mult'.
apply filterlim_ext with (2:=Hla); apply sum_n_Reals.
Admitted.

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
Admitted.

Lemma Series_minus (a b : nat -> R) : ex_series a -> ex_series b -> Series (fun n => a n - b n) = Series a - Series b.
Proof.
intros Ha Hb.
rewrite Series_plus => //.
rewrite Series_opp => //.
apply ex_series_opp in Hb.
now simpl in Hb.
