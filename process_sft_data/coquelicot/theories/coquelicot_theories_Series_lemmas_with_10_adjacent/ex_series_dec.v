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

Lemma is_series_unique (a : nat -> R) (l : R) : is_series a l -> Series a = l.
Proof.
move => Ha.
replace l with (real (Finite l)) by auto.
apply (f_equal real).
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
by exists l.
