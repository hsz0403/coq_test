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

Lemma Rbar_is_lub_sup_seq (u : nat -> Rbar) (l : Rbar) : Rbar_is_lub (fun x => exists n, x = u n) l -> is_sup_seq u l.
Proof.
destruct l as [l | | ] ; intros (ub, lub).
intro eps ; split.
intro n ; apply Rbar_le_lt_trans with (y := Finite l).
apply ub ; exists n ; auto.
pattern l at 1 ; rewrite <-(Rplus_0_r l) ; apply Rplus_lt_compat_l, eps.
apply LPO_notforall.
intro n.
destruct (Rbar_lt_dec (l - eps) (u n)) as [H|H].
now left.
now right.
intro H.
assert (H0 : (Rbar_is_upper_bound (fun x : Rbar => exists n : nat, x = u n) (Finite (l - eps)))).
intros x (n,Hn) ; rewrite Hn ; clear Hn ; apply Rbar_not_lt_le, H.
generalize (lub _ H0) ; clear lub ; apply Rbar_lt_not_le ; pattern l at 2 ; rewrite <-(Rplus_0_r l) ; apply Rplus_lt_compat_l, Ropp_lt_gt_0_contravar, eps.
intro M ; apply LPO_notforall.
intro n.
destruct (Rbar_lt_dec M (u n)) as [H|H].
now left.
now right.
intro H.
assert (H0 : Rbar_is_upper_bound (fun x : Rbar => exists n : nat, x = u n) (Finite M)).
intros x (n,Hn) ; rewrite Hn ; clear Hn ; apply Rbar_not_lt_le, H.
generalize (lub _ H0) ; clear lub ; apply Rbar_lt_not_le ; simpl ; auto.
intros M n.
apply Rbar_le_lt_trans with (y := m_infty) ; simpl ; auto.
apply ub ; exists n ; auto.
