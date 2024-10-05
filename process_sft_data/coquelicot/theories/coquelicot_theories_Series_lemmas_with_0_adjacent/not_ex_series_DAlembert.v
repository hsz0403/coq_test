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

Lemma not_ex_series_DAlembert (a : nat -> R) (l : R) : l > 1 -> (forall n, a n <> 0) -> is_lim_seq (fun n => Rabs (a (S n) / a n)) l -> ~ is_lim_seq a 0.
Proof.
move => Hl Ha Hda Ha0.
set k := (l+1)/2.
have Hk1 : 1 < k.
unfold k ; lra.
have : exists N, forall n, (N <= n)%nat -> k <= Rabs (a (S n) / a n).
apply is_lim_seq_spec in Hda.
case: (fun H => Hda (mkposreal ((l-1)/2) H)) => [ | /= {Hda} H N Hda].
apply Rdiv_lt_0_compat.
by apply -> Rminus_lt_0.
by apply Rlt_R0_R2.
exists N => n Hn.
move: (Hda n Hn) => {Hda} Hda.
apply Rabs_lt_between' in Hda.
replace (k) with (l - (l - 1) / 2) by (unfold k ; field).
by apply Rlt_le, Hda.
case => N H.
apply is_lim_seq_abs_0, (is_lim_seq_incr_n _ N) in Ha0.
have : forall n, Rabs (a N) * k ^ n <= Rabs (a (n + N)%nat).
elim => /= [ | n IH].
rewrite Rmult_1_r ; by apply Rle_refl.
replace (Rabs (a (S (n + N)))) with (Rabs (a (S (n+N)) / a (n+N)%nat) * Rabs (a (n+N)%nat)) by (rewrite -Rabs_mult ; apply f_equal ; by field).
replace (Rabs (a N) * (k * k ^ n)) with (k * (Rabs (a N) * k ^ n)) by ring.
apply Rmult_le_compat.
by apply Rlt_le, Rlt_trans with (1 := Rlt_0_1).
apply Rmult_le_pos.
by apply Rabs_pos.
apply pow_le.
by apply Rlt_le, Rlt_trans with (1 := Rlt_0_1).
by apply H, le_plus_r.
by apply IH.
move => {H} H.
have : Finite 0 = p_infty.
rewrite -(Lim_seq_geom_p k Hk1).
apply sym_equal.
apply is_lim_seq_unique.
apply is_lim_seq_ext with (fun n => / Rabs (a N) * (Rabs (a N) * k ^ n)).
move => n ; field ; by apply Rabs_no_R0.
rewrite -(Rmult_0_r (/Rabs (a N))).
apply (is_lim_seq_scal_l _ _ (Finite 0)).
apply is_lim_seq_le_le with (fun _ => 0) (fun n => Rabs (a (n + N)%nat)).
move => n ; split.
apply Rmult_le_pos.
by apply Rabs_pos.
apply pow_le.
by apply Rlt_le, Rlt_trans with (1 := Rlt_0_1).
by apply H.
by apply is_lim_seq_const.
by apply Ha0.
by [].
