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

Lemma is_LimSup_infSup_seq (u : nat -> R) (l : Rbar) : is_LimSup_seq u l <-> is_inf_seq (fun m => Sup_seq (fun n => u (n + m)%nat)) l.
Proof.
case: l => [l | | ] ; rewrite /is_LimSup_seq /is_inf_seq ; split => Hl.
split.
move => N.
apply Sup_seq_minor_lt.
case: (proj1 (Hl eps) N) => {Hl} n Hl.
exists (n - N)%nat.
rewrite MyNat.sub_add ; intuition.
case: (proj2 (Hl (pos_div_2 eps))) => /= {Hl} N Hl.
exists N ; rewrite /Sup_seq ; case: ex_sup_seq => un Hun ; simpl proj1_sig.
case: un Hun => [un | | ] /= Hun.
case: (proj2 (Hun (pos_div_2 eps))) => {Hun} /= n Hun.
apply Rlt_minus_l in Hun.
apply Rlt_trans with (1 := Hun).
apply Rlt_minus_r.
apply Rlt_le_trans with (1 := Hl _ (le_plus_r _ _)) ; right ; field.
case: (Hun (l + eps / 2)) => {Hun} n.
apply Rle_not_lt, Rlt_le, Hl, le_plus_r.
by [].
split.
move => N.
move: (proj1 (Hl eps) N) => {Hl} Hl.
apply Sup_seq_minor_lt in Hl.
case: Hl => /= n Hl.
exists (n + N)%nat ; intuition.
case: (proj2 (Hl eps)) => {Hl} N Hl.
exists N => n Hn.
apply (Rbar_not_le_lt (l + eps) (u n)).
contradict Hl.
apply Rbar_le_not_lt.
apply Sup_seq_minor_le with (n - N)%nat.
by rewrite MyNat.sub_add.
move => M N.
case: (Hl M N) => {Hl} n Hl.
apply Sup_seq_minor_lt.
exists (n - N)%nat.
rewrite MyNat.sub_add ; intuition.
move => M N.
move: (Hl M N) => {Hl} Hl.
apply Sup_seq_minor_lt in Hl.
case: Hl => /= n Hl.
exists (n + N)%nat ; intuition.
move => M.
case: (Hl (M-1)) => {Hl} N Hl.
exists N ; rewrite /Sup_seq ; case: ex_sup_seq => un Hun ; simpl proj1_sig.
case: un Hun => [un | | ] /= Hun.
case: (proj2 (Hun (mkposreal _ Rlt_0_1))) => {Hun} /= n Hun.
apply Rlt_minus_l in Hun.
apply Rlt_trans with (1 := Hun).
apply Rlt_minus_r.
apply Hl ; intuition.
case: (Hun (M-1)) => {Hun} n.
apply Rle_not_lt, Rlt_le, Hl, le_plus_r.
by [].
move => M.
case: (Hl M) => {Hl} N Hl.
exists N => n Hn.
apply (Rbar_not_le_lt M (u n)).
contradict Hl.
apply Rbar_le_not_lt.
apply Sup_seq_minor_le with (n - N)%nat.
by rewrite MyNat.sub_add.
