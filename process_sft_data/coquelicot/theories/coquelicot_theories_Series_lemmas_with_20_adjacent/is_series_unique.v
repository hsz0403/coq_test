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

Lemma ex_series_dec (a : nat -> R) : {ex_series a} + {~ ex_series a}.
Proof.
case: (ex_lim_seq_dec (sum_n a)) => H.
apply Lim_seq_correct in H.
case: (Lim_seq (sum_n a)) H => [l | | ] H.
left ; by exists l.
right ; case => l H0.
absurd (p_infty = Finite l) => //.
rewrite -(is_lim_seq_unique _ _ H).
by apply is_lim_seq_unique.
right ; case => l H0.
absurd (m_infty = Finite l) => //.
rewrite -(is_lim_seq_unique _ _ H).
by apply is_lim_seq_unique.
right ; case => l.
contradict H.
Admitted.

Lemma Series_correct (a : nat -> R) : ex_series a -> is_series a (Series a).
Proof.
case => l Ha.
Admitted.

Lemma is_series_Reals (a : nat -> R) (l : R) : is_series a l <-> infinite_sum a l.
Proof.
split => H.
apply (is_lim_seq_spec _ l) in H.
move => e He ; set eps := mkposreal e He.
case: (H eps) => /= {H} N H.
exists N => n Hn.
rewrite <- sum_n_Reals.
by apply (H n Hn).
apply (is_lim_seq_spec _ l).
move => eps.
case: (H eps (cond_pos eps)) => {H} N H.
exists N => n Hn.
rewrite sum_n_Reals.
Admitted.

Lemma ex_series_Reals_0 (a : nat -> R) : ex_series a -> { l:R | Un_cv (fun N:nat => sum_f_R0 a N) l }.
Proof.
move => H ; exists (Series a) ; case: H => l H.
replace (Series a) with l.
move => e He ; set eps := mkposreal e He.
apply (is_lim_seq_spec _ l) in H.
case: (H eps) => /= {H} N H.
exists N => n Hn.
rewrite <- sum_n_Reals.
by apply (H n Hn).
apply sym_eq.
rewrite /Series.
replace l with (real (Finite l)) by auto.
apply f_equal.
Admitted.

Lemma ex_series_Reals_1 (a : nat -> R) : { l:R | Un_cv (fun N:nat => sum_f_R0 a N) l } -> ex_series a.
Proof.
case => l H.
exists l.
apply (is_lim_seq_spec _ l).
move => eps.
case: (H eps (cond_pos eps)) => {H} N H.
exists N => n Hn.
rewrite sum_n_Reals.
Admitted.

Lemma Cauchy_ex_series {K : AbsRing} {V : CompleteNormedModule K} (a : nat -> V) : ex_series a -> Cauchy_series a.
Proof.
intros [l Hl] eps.
set (eps' := eps / (norm_factor (V := V))).
assert (He: 0 < eps').
apply Rdiv_lt_0_compat.
apply eps.
apply norm_factor_gt_0.
destruct (proj2 (filterlim_locally_cauchy (U := V) (F := eventually) (sum_n (fun k => a k))) (ex_intro _ l Hl) (mkposreal _ He)) as [P [[N HN] HP]].
exists (S N).
intros [|u] v Hu Hv.
elim le_Sn_O with (1 := Hu).
destruct (le_or_lt u v) as [Huv|Huv].
rewrite -> sum_n_m_sum_n with (1 := Huv).
replace (pos eps) with (norm_factor (V := V) * mkposreal _ He).
apply norm_compat2.
apply HP ; apply HN.
now apply le_S_n.
now apply le_Sn_le.
rewrite /eps' /=.
field.
apply Rgt_not_eq, norm_factor_gt_0.
rewrite sum_n_m_zero.
rewrite norm_zero.
apply cond_pos.
Admitted.

Lemma ex_series_Cauchy {K : AbsRing} {V : CompleteNormedModule K} (a : nat -> V) : Cauchy_series a -> ex_series a.
Proof.
intros Ca.
destruct (proj1 (filterlim_locally_cauchy (U := V) (F := eventually) (sum_n a))) as [l Hl].
2: now exists l.
intros eps.
destruct (Ca eps) as [N HN].
exists (le N).
split.
now exists N.
intros u v.
wlog Huv: u v / (u <= v)%nat.
intros H.
destruct (le_or_lt u v) as [Huv|Huv].
now apply H.
intros Hu Hv.
apply ball_sym.
apply H => //.
now apply lt_le_weak.
intros Hu Hv.
apply: norm_compat1.
rewrite <- sum_n_m_sum_n with (1 := Huv).
apply HN => //.
Admitted.

Lemma is_series_ext (a b : nat -> V) (l : V) : (forall n, a n = b n) -> (is_series a l) -> is_series b l.
Proof.
move => Heq.
apply filterlim_ext.
Admitted.

Lemma ex_series_ext (a b : nat -> V) : (forall n, a n = b n) -> ex_series a -> ex_series b.
Proof.
move => Heq [l Ha].
Admitted.

Lemma Series_ext (a b : nat -> R) : (forall n, a n = b n) -> Series a = Series b.
Proof.
move => Heq.
apply (f_equal real).
apply Lim_seq_ext.
Admitted.

Lemma is_series_incr_1 (a : nat -> V) (l : V) : is_series a (plus l (a O)) -> is_series (fun k => a (S k)%nat) l.
Proof.
intros H.
apply filterlim_ext with (fun k => plus (sum_n a (S k)) (opp (a 0%nat))).
induction x; simpl.
rewrite sum_Sn !sum_O (plus_comm _ (a 1%nat)); rewrite <- plus_assoc.
now rewrite plus_opp_r plus_zero_r.
rewrite !sum_Sn -IHx -!sum_Sn sum_Sn; simpl.
rewrite <- plus_assoc, <- (plus_assoc _ _ (a (S (S x)))).
apply f_equal; apply plus_comm.
apply filterlim_comp with (G:=(locally (plus l (a 0%nat)))) (g:=fun x => plus x (opp (a 0%nat))).
apply filterlim_comp with (f:= fun x => S x) (2:=H).
apply eventually_subseq; intros n; omega.
pattern l at 2; replace l with (plus (plus l (a 0%nat)) (opp (a 0%nat))).
apply filterlim_comp_2 with (3 := filterlim_plus _ _).
apply filterlim_id.
apply filterlim_const.
rewrite <- plus_assoc, plus_opp_r.
Admitted.

Lemma is_series_incr_n (a : nat -> V) (n : nat) (l : V) : (0 < n)%nat -> is_series a (plus l (sum_n a (pred n))) -> is_series (fun k => a (n + k)%nat) l.
Proof.
case: n => /= [ | n] Hn Ha.
by apply lt_irrefl in Hn.
clear Hn.
elim: n l Ha => [ | n IH] l Ha.
rewrite sum_O in Ha.
by apply is_series_incr_1.
apply is_series_ext with (fun k : nat => a (S (n + S k))).
move => k ; apply f_equal ; ring.
apply (is_series_incr_1 (fun k : nat => a (S (n + k))) l).
rewrite plus_0_r.
apply IH.
replace (plus (plus l (a (S n))) (sum_n a n)) with (plus l (sum_n a (S n))).
assumption.
Admitted.

Lemma is_series_decr_1 (a : nat -> V) (l : V) : is_series (fun k => a (S k)%nat) (plus l (opp (a O))) -> is_series a l.
Proof.
intros H.
apply filterlim_ext_loc with (fun v => plus (a 0%nat) (sum_n (fun k : nat => a (S k)) (pred v))).
exists 1%nat.
intros n Hn; apply sym_eq.
rewrite /sum_n sum_Sn_m.
apply f_equal.
rewrite sum_n_m_S.
apply f_equal ; omega.
by apply le_O_n.
replace l with (plus (a 0%nat) (plus l (opp (a 0%nat)))).
apply filterlim_comp_2 with (3 := filterlim_plus _ _).
apply filterlim_id.
apply filterlim_const.
apply filterlim_comp with (f:= fun x => pred x) (2:=H).
intros P (N1,HN1).
exists (S N1).
intros n Hn; apply HN1; omega.
rewrite plus_comm; rewrite <- plus_assoc.
rewrite (plus_comm _ (a 0%nat)); rewrite plus_opp_r.
Admitted.

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

Lemma is_series_unique (a : nat -> R) (l : R) : is_series a l -> Series a = l.
Proof.
move => Ha.
replace l with (real (Finite l)) by auto.
apply (f_equal real).
by apply is_lim_seq_unique.
