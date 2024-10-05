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

Lemma ex_finite_lim_seq_decr (u : nat -> R) (M : R) : (forall n, (u (S n)) <= (u n)) -> (forall n, M <= u n) -> ex_finite_lim_seq u.
Proof.
intros.
apply ex_finite_lim_seq_correct.
have H1 : ex_lim_seq u.
exists (real (Inf_seq u)).
apply is_lim_seq_spec.
rewrite /Inf_seq ; case: ex_inf_seq ; case => [l | | ] //= Hl.
move => eps ; case: (Hl eps) => Hl1 [N Hl2].
exists N => n Hn.
apply Rabs_lt_between' ; split.
by apply Hl1.
apply Rle_lt_trans with (2 := Hl2).
elim: n N {Hl2} Hn => [ | n IH] N Hn.
rewrite (le_n_O_eq _ Hn).
apply Rle_refl.
apply le_lt_eq_dec in Hn.
case: Hn => [Hn | ->].
apply Rle_trans with (1 := H _), IH ; intuition.
by apply Rle_refl.
move: (Hl (u O) O) => H1 ; by apply Rlt_irrefl in H1.
case: (Hl M) => {Hl} n Hl.
apply Rlt_not_le in Hl.
by move: (Hl (H0 n)).
split => //.
apply Lim_seq_correct in H1.
case: (Lim_seq u) H1 => [l | | ] /= Hu.
by [].
apply is_lim_seq_spec in Hu.
case: (Hu (u O)) => {Hu} N Hu.
move: (Hu N (le_refl _)) => {Hu} Hu.
contradict Hu ; apply Rle_not_lt.
elim: N => [ | N IH].
by apply Rle_refl.
by apply Rle_trans with (1 := H _).
apply is_lim_seq_spec in Hu.
case: (Hu M) => {Hu} N Hu.
move: (Hu N (le_refl _)) => {Hu} Hu.
contradict Hu ; by apply Rle_not_lt.
