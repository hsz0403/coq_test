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
apply filterlim_ext with (2:=Hlb); apply sum_n_Reals.
