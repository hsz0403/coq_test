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

Lemma Lim_seq_scal_l (u : nat -> R) (a : R) : Lim_seq (fun n => a * u n) = Rbar_mult a (Lim_seq u).
Proof.
case: (Req_dec a 0) => [ -> | Ha].
rewrite -(Lim_seq_ext (fun _ => 0)) /=.
rewrite Lim_seq_const.
case: (Lim_seq u) => [x | | ] //=.
by rewrite Rmult_0_l.
case: Rle_dec (Rle_refl 0) => // H _.
case: Rle_lt_or_eq_dec (Rlt_irrefl 0) => // _ _.
case: Rle_dec (Rle_refl 0) => // H _.
case: Rle_lt_or_eq_dec (Rlt_irrefl 0) => // _ _.
move => n ; by rewrite Rmult_0_l.
wlog: a u Ha / (0 < a) => [Hw | {Ha} Ha].
case: (Rlt_le_dec 0 a) => Ha'.
by apply Hw.
case: Ha' => // Ha'.
rewrite -(Lim_seq_ext (fun n => - a * - u n)).
rewrite -Rbar_mult_opp.
rewrite -Lim_seq_opp.
apply Hw.
contradict Ha ; rewrite -(Ropp_involutive a) Ha ; ring.
apply Ropp_lt_cancel ; by rewrite Ropp_0 Ropp_involutive.
move => n ; ring.
rewrite /Lim_seq.
rewrite {2}/LimSup_seq ; case: ex_LimSup_seq => ls Hs ; rewrite {2}/LimInf_seq ; case: ex_LimInf_seq => li Hi ; simpl proj1_sig.
apply (is_LimSup_seq_scal_pos a) in Hs => //.
apply (is_LimInf_seq_scal_pos a) in Hi => //.
rewrite (is_LimSup_seq_unique _ _ Hs).
rewrite (is_LimInf_seq_unique _ _ Hi).
case: ls {Hs} => [ls | | ] ; case: li {Hi} => [li | | ] //= ; case: (Rle_dec 0 a) (Rlt_le _ _ Ha) => // Ha' _ ; case: (Rle_lt_or_eq_dec 0 a Ha') (Rlt_not_eq _ _ Ha) => //= _ _ ; apply f_equal ; field.
