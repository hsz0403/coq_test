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

Lemma is_sup_seq_lub (u : nat -> Rbar) (l : Rbar) : is_sup_seq u l -> Rbar_is_lub (fun x => exists n, x = u n) l.
Proof.
destruct l as [l | | ] ; intro Hl ; split.
intro x ; destruct x as [x | | ] ; simpl ; intros (n, Hn).
apply le_epsilon ; intros e He ; set (eps := mkposreal e He).
change (Rbar_le x (l + e)).
rewrite Hn ; apply Rbar_lt_le, (Hl eps).
now generalize (proj1 (Hl (mkposreal _ Rlt_0_1)) n) ; clear Hl ; simpl ; intros Hl ; rewrite <-Hn in Hl.
easy.
intros b ; destruct b as [b | | ] ; intros Hb ; apply Rbar_not_lt_le ; auto ; intros He.
set (eps := mkposreal _ (Rlt_Rminus _ _ He)) ; case (proj2 (Hl eps)) ; clear Hl ; intros n.
apply Rbar_le_not_lt ; assert (l - eps = b) .
simpl ; ring.
rewrite H ; clear H ; apply Hb ; exists n ; auto.
generalize (Rbar_ub_m_infty _ Hb) ; clear Hb ; intros Hb.
case (proj2 (Hl (mkposreal _ Rlt_0_1))) ; clear Hl ; simpl ; intros n Hl.
assert (H : (exists n0 : nat, u n = u n0)).
exists n ; auto.
generalize (Hb (u n) H) Hl ; clear Hb ; now case (u n).
apply Rbar_ub_p_infty.
intro b ; destruct b as [b | | ] ; simpl ; intro Hb.
case (Hl b) ; clear Hl ; intros n Hl.
contradict Hl ; apply Rbar_le_not_lt, Hb ; exists n ; auto.
easy.
generalize (Rbar_ub_m_infty _ Hb) ; clear Hb ; intro Hb.
case (Hl 0) ; clear Hl; intros n Hl.
assert (H : (exists n0 : nat, u n = u n0)).
exists n ; auto.
generalize (Hb (u n) H) Hl ; clear Hl ; now case (u n).
intro x ; destruct x as [x | | ] ; intros (n, Hx).
generalize (Hl x n) ; clear Hl ; intro Hl ; rewrite <-Hx in Hl ; apply Rlt_irrefl in Hl ; intuition.
generalize (Hl 0 n) ; rewrite <-Hx ; intuition.
easy.
now intros b ; destruct b as [b | | ].
