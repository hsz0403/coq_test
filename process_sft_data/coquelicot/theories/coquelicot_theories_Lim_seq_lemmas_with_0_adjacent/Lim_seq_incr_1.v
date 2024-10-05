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

Lemma Lim_seq_incr_1 (u : nat -> R) : Lim_seq (fun n => u (S n)) = Lim_seq u.
Proof.
rewrite /Lim_seq.
replace (LimSup_seq (fun n : nat => u (S n))) with (LimSup_seq u).
replace (LimInf_seq (fun n : nat => u (S n))) with (LimInf_seq u).
by [].
rewrite /LimInf_seq ; case: ex_LimInf_seq => l1 H1 ; case: ex_LimInf_seq => l2 H2 /= ; case: l1 H1 => [l1 | | ] /= H1 ; case: l2 H2 => [l2 | | ] /= H2.
apply Rbar_finite_eq, Rle_antisym ; apply le_epsilon => e He ; set eps := mkposreal e He ; apply Rlt_le.
case: (proj2 (H1 (pos_div_2 eps))) => /= {H1} N H1.
case: (proj1 (H2 (pos_div_2 eps)) N) => /= {H2} n [Hn H2].
apply Rlt_trans with (u (S n) + e/2).
replace l1 with ((l1-e/2)+e/2) by ring.
apply Rplus_lt_compat_r.
apply H1.
apply le_trans with (1 := Hn).
apply le_n_Sn.
replace (l2+e) with ((l2+e/2)+e/2) by field.
by apply Rplus_lt_compat_r, H2.
case: (proj2 (H2 (pos_div_2 eps))) => /= {H2} N H2.
case: (proj1 (H1 (pos_div_2 eps)) (S N)) => /= {H1} .
case => [ | n] [Hn H1].
by apply le_Sn_0 in Hn.
apply Rlt_trans with (u (S n) + e/2).
replace l2 with ((l2-e/2)+e/2) by ring.
apply Rplus_lt_compat_r.
apply H2.
by apply le_S_n, Hn.
replace (l1+e) with ((l1+e/2)+e/2) by field.
by apply Rplus_lt_compat_r, H1.
have : False => //.
case: (H2 (l1+1)) => {H2} N /= H2.
case: (proj1 (H1 (mkposreal _ Rlt_0_1)) (S N)) ; case => /= {H1} [ | n] [Hn].
by apply le_Sn_0 in Hn.
apply Rle_not_lt, Rlt_le, H2.
by apply le_S_n.
have : False => //.
case: (proj2 (H1 (mkposreal _ Rlt_0_1))) => {H1} N /= H1.
case: ((H2 (l1-1)) N) => /= {H2} n [Hn].
apply Rle_not_lt, Rlt_le, H1.
by apply le_trans with (2 := le_n_Sn _).
have : False => //.
case: (H1 (l2+1)) => {H1} N /= H1.
case: (proj1 (H2 (mkposreal _ Rlt_0_1)) N) => /= {H2} n [Hn].
apply Rle_not_lt, Rlt_le, H1.
by apply le_trans with (2 := le_n_Sn _).
by [].
have : False => //.
case: (H1 0) => {H1} N H1.
case: (H2 0 N)=> {H2} n [Hn].
apply Rle_not_lt, Rlt_le, H1.
by apply le_trans with (2 := le_n_Sn _).
have : False => //.
case: (proj2 (H2 (mkposreal _ Rlt_0_1))) => /= {H2} N H2.
case: (H1 (l2-1) (S N)) ; case => [ | n] [Hn].
by apply le_Sn_0 in Hn.
by apply Rle_not_lt, Rlt_le, H2, le_S_n.
have : False => //.
case: (H2 0) => {H2} N H2.
case: (H1 0 (S N)) ; case => [ | n] [Hn].
by apply le_Sn_0 in Hn.
by apply Rle_not_lt, Rlt_le, H2, le_S_n.
by [].
rewrite /LimSup_seq ; case: ex_LimSup_seq => l1 H1 ; case: ex_LimSup_seq => l2 H2 /= ; case: l1 H1 => [l1 | | ] /= H1 ; case: l2 H2 => [l2 | | ] /= H2.
apply Rbar_finite_eq, Rle_antisym ; apply le_epsilon => e He ; set eps := mkposreal e He ; apply Rlt_le.
case: (proj2 (H2 (pos_div_2 eps))) => /= {H2} N H2.
case: ((proj1 (H1 (pos_div_2 eps))) (S N)) ; case => /= {H1} [ | n] [Hn H1].
by apply le_Sn_0 in Hn.
replace l1 with ((l1-e/2)+e/2) by ring.
replace (l2+e) with ((l2+e/2)+e/2) by field.
apply Rplus_lt_compat_r.
apply Rlt_trans with (1 := H1).
by apply H2, le_S_n.
case: (proj2 (H1 (pos_div_2 eps))) => /= {H1} N H1.
case: ((proj1 (H2 (pos_div_2 eps))) N) => /= {H2} n [Hn H2].
replace l2 with ((l2-e/2)+e/2) by ring.
replace (l1+e) with ((l1+e/2)+e/2) by field.
apply Rplus_lt_compat_r.
apply Rlt_trans with (1 := H2).
by apply H1, le_trans with (2 := le_n_Sn _).
have : False => //.
case: (proj2 (H1 (mkposreal _ Rlt_0_1))) => /= {H1} N H1.
case: (H2 (l1+1) N) => n [Hn].
by apply Rle_not_lt, Rlt_le, H1, le_trans with (2 := le_n_Sn _).
have : False => //.
case: (H2 (l1-1)) => {H2} N H2.
case: (proj1 (H1 (mkposreal _ Rlt_0_1)) (S N)) ; case => [ | n] [Hn] /= .
by apply le_Sn_0 in Hn.
by apply Rle_not_lt, Rlt_le, H2, le_S_n.
have : False => //.
case: (proj2 (H2 (mkposreal _ Rlt_0_1))) => {H2} /= N H2.
case: (H1 (l2+1) (S N)) ; case => [ | n] [Hn] /= .
by apply le_Sn_0 in Hn.
by apply Rle_not_lt, Rlt_le, H2, le_S_n.
by [].
have : False => //.
case: (H2 0) => {H2} N H2.
case: (H1 0 (S N)) ; case => [ | n] [Hn] /= .
by apply le_Sn_0 in Hn.
by apply Rle_not_lt, Rlt_le, H2, le_S_n.
have : False => //.
case: (H1 (l2-1)) => {H1} N H1.
case: (proj1 (H2 (mkposreal _ Rlt_0_1)) N) => /= {H2} n [Hn].
by apply Rle_not_lt, Rlt_le, H1, le_trans with (2 := le_n_Sn _).
have : False => //.
case: (H1 0) => {H1} N H1.
case: (H2 0 N) => {H2} n [Hn].
by apply Rle_not_lt, Rlt_le, H1, le_trans with (2 := le_n_Sn _).
by [].
