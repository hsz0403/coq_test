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

Lemma is_LimSup_seq_ind_1 (u : nat -> R) (l : Rbar) : is_LimSup_seq u l <-> is_LimSup_seq (fun n => u (S n)) l.
Proof.
case: l => [l | | ] ; split => //= Hu.
move => eps.
case: (Hu eps) => {Hu} H1 H2 ; split.
move => N.
case: (H1 (S N)) => {H1} n [Hn H1].
exists (pred n).
case: (n) Hn H1 => /= [ | m] Hm H1.
by apply le_Sn_O in Hm.
split.
by apply le_S_n.
by apply H1.
case: H2 => N H2.
exists N => n Hn.
apply H2 ; intuition.
move => eps.
case: (Hu eps) => {Hu} H1 H2 ; split.
move => N.
case: (H1 N) => {H1} n [Hn H1].
exists (S n) ; intuition.
case: H2 => N H2.
exists (S N) => n Hn.
case: (n) Hn => /= [ | m] Hm.
by apply le_Sn_O in Hm.
apply H2 ; intuition.
move => M N.
case: (Hu M (S N)) => {Hu} n [Hn Hu].
exists (pred n).
case: (n) Hn Hu => /= [ | m] Hm Hu.
by apply le_Sn_O in Hm.
split.
by apply le_S_n.
by apply Hu.
move => M N.
case: (Hu M N) => {Hu} n [Hn Hu].
exists (S n) ; intuition.
move => M.
case: (Hu M) => {Hu} N Hu.
exists N => n Hn.
apply Hu ; intuition.
move => M.
case: (Hu M) => {Hu} N Hu.
exists (S N) => n Hn.
case: (n) Hn => /= [ | m] Hm.
by apply le_Sn_O in Hm.
apply Hu ; intuition.
