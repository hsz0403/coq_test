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

Lemma LimSup_le (u v : nat -> R) : eventually (fun n => u n <= v n) -> Rbar_le (LimSup_seq u) (LimSup_seq v).
Proof.
intros (N,H).
rewrite /LimSup_seq.
case: ex_LimSup_seq ; case => [lu | | ] //= Hlu ; case: ex_LimSup_seq ; case => [lv | | ] //= Hlv.
apply Rnot_lt_le => Hl.
apply Rminus_lt_0 in Hl.
case: (Hlv (pos_div_2 (mkposreal _ Hl))) => {Hlv} /= _ [n Hlv].
case: (proj1 (Hlu (pos_div_2 (mkposreal _ Hl))) (N + n)%nat) => {Hlu} m /= [Hm Hlu].
move: (H _ (le_trans _ _ _ (le_plus_l _ _) Hm)).
apply Rlt_not_le.
eapply Rlt_trans, Hlu.
eapply Rlt_le_trans.
eapply Hlv, le_trans, Hm.
by apply le_plus_r.
apply Req_le ; field.
case: (Hlv (lu - 1)) => {Hlv} n Hlv.
case: (proj1 (Hlu (mkposreal _ Rlt_0_1)) (N + n)%nat) => {Hlu} m /= [Hm Hlu].
move: (H _ (le_trans _ _ _ (le_plus_l _ _) Hm)).
apply Rlt_not_le.
eapply Rlt_trans, Hlu.
eapply Hlv, le_trans, Hm.
by apply le_plus_r.
case: (Hlv (mkposreal _ Rlt_0_1)) => {Hlv} /= _ [n Hlv].
case: (Hlu (lv + 1) (N + n)%nat) => {Hlu} /= m [Hm Hlu].
move: (H _ (le_trans _ _ _ (le_plus_l _ _) Hm)).
apply Rlt_not_le.
eapply Rlt_trans, Hlu.
eapply Hlv, le_trans, Hm.
by apply le_plus_r.
case: (Hlv 0) => {Hlv} n Hlv.
case: (Hlu 0 (N + n)%nat) => {Hlu} m [Hm Hlu].
move: (H _ (le_trans _ _ _ (le_plus_l _ _) Hm)).
apply Rlt_not_le.
eapply Rlt_trans, Hlu.
eapply Hlv, le_trans, Hm.
by apply le_plus_r.
