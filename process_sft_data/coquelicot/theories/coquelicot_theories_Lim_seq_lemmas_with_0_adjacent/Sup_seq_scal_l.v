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

Lemma Sup_seq_scal_l (a : R) (u : nat -> Rbar) : 0 <= a -> Sup_seq (fun n => Rbar_mult a (u n)) = Rbar_mult a (Sup_seq u).
Proof.
case => Ha.
rewrite /Sup_seq.
case: ex_sup_seq => al Hau.
case: ex_sup_seq => l Hu.
simpl proj1_sig.
apply Rbar_le_antisym.
apply is_sup_seq_lub in Hau.
apply is_sup_seq_lub in Hu.
apply Hau => _ [n ->].
suff : Rbar_le (u n) l.
case: (u n) => [un | | ] ; case: (l) => [l' | | ] /= ; try (by case) ; try (case: Rle_dec (Rlt_le _ _ Ha) => //= Ha' _ ; case: Rle_lt_or_eq_dec (Rlt_not_eq _ _ Ha) => //= _ _ _ ; by left).
intros H ; apply Rmult_le_compat_l => // ; by apply Rlt_le.
apply Hu.
by exists n.
suff : Rbar_le l (Rbar_div_pos al (mkposreal a Ha)).
case: (al) => [al' | | ] ; case: (l) => [l' | | ] /= ; try (by case) ; try (case: Rle_dec (Rlt_le _ _ Ha) => //= Ha' _ ; case: Rle_lt_or_eq_dec (Rlt_not_eq _ _ Ha) => //= _ _ _ ; by left).
intros H ; rewrite Rmult_comm ; apply Rle_div_r => //.
apply is_sup_seq_lub in Hau.
apply is_sup_seq_lub in Hu.
apply Hu => _ [n ->].
suff : Rbar_le (Rbar_mult a (u n)) al.
case: (u n) => [un | | ] ; case: (al) => [al' | | ] /= ; try (by case) ; try (case: Rle_dec (Rlt_le _ _ Ha) => //= Ha' _ ; case: Rle_lt_or_eq_dec (Rlt_not_eq _ _ Ha) => //= _ _ ; try (by case) ; by left).
intros H ; rewrite Rmult_comm in H ; apply Rle_div_r => //.
apply Hau.
by exists n.
rewrite -Ha.
transitivity (Sup_seq (fun _ => 0)).
apply Sup_seq_ext.
move => n ; case: (u n) => [un | | ] /=.
apply f_equal ; ring.
case: Rle_dec (Rle_refl 0) => //= H _.
case: Rle_lt_or_eq_dec (Rle_not_lt _ _ H) => //= H _.
case: Rle_dec (Rle_refl 0) => //= H _.
case: Rle_lt_or_eq_dec (Rle_not_lt _ _ H) => //= H _.
transitivity 0.
apply is_sup_seq_unique.
move => eps ; split => /=.
move => _ ; ring_simplify ; by apply eps.
exists 0%nat ; apply Rminus_lt_0 ; ring_simplify ; by apply eps.
case: (Sup_seq u) => [l | | ] /=.
apply f_equal ; ring.
case: Rle_dec (Rle_refl 0) => //= H _.
case: Rle_lt_or_eq_dec (Rle_not_lt _ _ H) => //= H _.
case: Rle_dec (Rle_refl 0) => //= H _.
case: Rle_lt_or_eq_dec (Rle_not_lt _ _ H) => //= H _.
