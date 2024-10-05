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

Lemma ex_lim_seq_cauchy_corr (u : nat -> R) : (ex_finite_lim_seq u) <-> ex_lim_seq_cauchy u.
Proof.
split => Hcv.
apply Lim_seq_correct' in Hcv.
apply is_lim_seq_spec in Hcv.
move => eps.
case: (Hcv (pos_div_2 eps)) => /= {Hcv} N H.
exists N => n m Hn Hm.
replace (u n - u m) with ((u n - (real (Lim_seq u))) - (u m - (real (Lim_seq u)))) by ring.
apply Rle_lt_trans with (1 := Rabs_triang _ _).
rewrite Rabs_Ropp (double_var eps).
apply Rplus_lt_compat ; by apply H.
exists (LimSup_seq u).
apply is_lim_seq_spec.
intros eps.
rewrite /LimSup_seq ; case: ex_LimSup_seq => /= l Hl.
case: (Hcv (pos_div_2 eps)) => {Hcv} /= Ncv Hcv.
case: l Hl => [l | | ] /= Hl.
case: (Hl (pos_div_2 eps)) => {Hl} /= H1 [Nl H2].
exists (Ncv + Nl)%nat => n Hn.
apply Rabs_lt_between' ; split.
case: (H1 Ncv) => {H1} m [Hm H1].
replace (l - eps) with ((l - eps / 2) - eps / 2) by field.
apply Rlt_trans with (u m - eps / 2).
by apply Rplus_lt_compat_r.
apply Rabs_lt_between'.
apply Hcv ; intuition.
apply Rlt_trans with (l + eps / 2).
apply H2 ; intuition.
apply Rminus_lt_0 ; field_simplify ; rewrite ?Rdiv_1.
by apply is_pos_div_2.
move: (fun n Hn => proj2 (proj1 (Rabs_lt_between' _ _ _) (Hcv n Ncv Hn (le_refl _)))) => {Hcv} Hcv.
case: (Hl (u Ncv + eps / 2) Ncv) => {Hl} n [Hn Hl].
contradict Hl ; apply Rle_not_lt, Rlt_le.
by apply Hcv.
move: (fun n Hn => proj1 (proj1 (Rabs_lt_between' _ _ _) (Hcv n Ncv Hn (le_refl _)))) => {Hcv} Hcv.
case: (Hl (u Ncv - eps / 2)) => {Hl} N Hl.
move: (Hcv _ (le_plus_l Ncv N)) => H.
contradict H ; apply Rle_not_lt, Rlt_le, Hl, le_plus_r.
