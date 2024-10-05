Require Import Reals Psatz.
Require Import mathcomp.ssreflect.ssreflect.
Require Import Rcomplements.
Require Import Rbar Lub Markov Hierarchy.
Open Scope R_scope.
Definition is_sup_seq (u : nat -> Rbar) (l : Rbar) := match l with | Finite l => forall (eps : posreal), (forall n, Rbar_lt (u n) (l+eps)) /\ (exists n, Rbar_lt (l-eps) (u n)) | p_infty => forall M : R, exists n, Rbar_lt M (u n) | m_infty => forall M : R, forall n, Rbar_lt (u n) M end.
Definition is_inf_seq (u : nat -> Rbar) (l : Rbar) := match l with | Finite l => forall (eps : posreal), (forall n, Rbar_lt (Finite (l-eps)) (u n)) /\ (exists n, Rbar_lt (u n) (Finite (l+eps))) | p_infty => forall M : R, forall n, Rbar_lt (Finite M) (u n) | m_infty => forall M : R, exists n, Rbar_lt (u n) (Finite M) end.
Definition Sup_seq (u : nat -> Rbar) := proj1_sig (ex_sup_seq u).
Definition Inf_seq (u : nat -> Rbar) := proj1_sig (ex_inf_seq u).
Definition is_LimSup_seq (u : nat -> R) (l : Rbar) := match l with | Finite l => forall eps : posreal, (forall N : nat, exists n : nat, (N <= n)%nat /\ l - eps < u n) /\ (exists N : nat, forall n : nat, (N <= n)%nat -> u n < l + eps) | p_infty => forall M : R, (forall N : nat, exists n : nat, (N <= n)%nat /\ M < u n) | m_infty => forall M : R, (exists N : nat, forall n : nat, (N <= n)%nat -> u n < M) end.
Definition is_LimInf_seq (u : nat -> R) (l : Rbar) := match l with | Finite l => forall eps : posreal, (forall N : nat, exists n : nat, (N <= n)%nat /\ u n < l + eps) /\ (exists N : nat, forall n : nat, (N <= n)%nat -> l - eps < u n) | p_infty => forall M : R, (exists N : nat, forall n : nat, (N <= n)%nat -> M < u n) | m_infty => forall M : R, (forall N : nat, exists n : nat, (N <= n)%nat /\ u n < M) end.
Definition LimSup_seq (u : nat -> R) := proj1_sig (ex_LimSup_seq u).
Definition LimInf_seq (u : nat -> R) := proj1_sig (ex_LimInf_seq u).
Definition is_lim_seq (u : nat -> R) (l : Rbar) := filterlim u eventually (Rbar_locally l).
Definition is_lim_seq' (u : nat -> R) (l : Rbar) := match l with | Finite l => forall eps : posreal, eventually (fun n => Rabs (u n - l) < eps) | p_infty => forall M : R, eventually (fun n => M < u n) | m_infty => forall M : R, eventually (fun n => u n < M) end.
Definition ex_lim_seq (u : nat -> R) := exists l, is_lim_seq u l.
Definition ex_finite_lim_seq (u : nat -> R) := exists l : R, is_lim_seq u l.
Definition Lim_seq (u : nat -> R) : Rbar := Rbar_div_pos (Rbar_plus (LimSup_seq u) (LimInf_seq u)) {| pos := 2; cond_pos := Rlt_R0_R2 |}.
Definition ex_lim_seq_cauchy (u : nat -> R) := forall eps : posreal, exists N : nat, forall n m, (N <= n)%nat -> (N <= m)%nat -> Rabs (u n - u m) < eps.

Lemma ex_lim_seq_adj (u v : nat -> R) : (forall n, u n <= u (S n)) -> (forall n, v (S n) <= v n) -> is_lim_seq (fun n => v n - u n) 0 -> ex_finite_lim_seq u /\ ex_finite_lim_seq v /\ Lim_seq u = Lim_seq v.
Proof.
move => Hu Hv H0.
suff H : forall n, u n <= v n.
suff Eu : ex_finite_lim_seq u.
split ; try auto.
suff Ev : ex_finite_lim_seq v.
split ; try auto.
apply is_lim_seq_unique in H0.
rewrite Lim_seq_minus in H0 ; try by intuition.
apply ex_finite_lim_seq_correct in Eu.
apply ex_finite_lim_seq_correct in Ev.
rewrite -(proj2 Eu) -(proj2 Ev) /= in H0 |- *.
apply Rbar_finite_eq in H0 ; apply Rbar_finite_eq.
by apply sym_eq, Rminus_diag_uniq, H0.
by apply ex_finite_lim_seq_correct.
by apply ex_finite_lim_seq_correct.
apply ex_finite_lim_seq_correct in Eu.
apply ex_finite_lim_seq_correct in Ev.
by rewrite -(proj2 Eu) -(proj2 Ev).
apply ex_finite_lim_seq_decr with (u O) => //.
move => n ; apply Rle_trans with (2 := H _).
elim: n => [ | n IH].
by apply Rle_refl.
by apply Rle_trans with (2 := Hu _).
apply ex_finite_lim_seq_incr with (v O) => //.
move => n ; apply Rle_trans with (1 := H _).
elim: n => [ | n IH].
by apply Rle_refl.
by apply Rle_trans with (1 := Hv _).
move => n0 ; apply Rnot_lt_le ; move/Rminus_lt_0 => H.
apply is_lim_seq_spec in H0.
case: (H0 (mkposreal _ H)) => /= {H0} N H0.
move: (H0 _ (le_plus_r n0 N)) ; apply Rle_not_lt.
rewrite Rminus_0_r ; apply Rle_trans with (2 := Rabs_maj2 _).
rewrite Ropp_minus_distr'.
apply Rplus_le_compat, Ropp_le_contravar.
elim: (N) => [ | m IH].
rewrite plus_0_r ; apply Rle_refl.
rewrite -plus_n_Sm ; by apply Rle_trans with (2 := Hu _).
elim: (N) => [ | m IH].
rewrite plus_0_r ; apply Rle_refl.
rewrite -plus_n_Sm ; by apply Rle_trans with (1 := Hv _).
