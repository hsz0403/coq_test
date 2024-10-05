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

Lemma filterlim_Rbar_inv : forall l : Rbar, l <> 0 -> filterlim Rinv (Rbar_locally l) (Rbar_locally (Rbar_inv l)).
Proof.
intros l.
wlog: l / (Rbar_lt 0 l).
intros Hw.
case: (Rbar_lt_le_dec 0 l) => Hl.
by apply Hw.
case: (Rbar_le_lt_or_eq_dec _ _ Hl) => // {Hl} Hl Hl0.
rewrite -(Rbar_opp_involutive (Rbar_inv l)).
replace (Rbar_opp (Rbar_inv l)) with (Rbar_inv (Rbar_opp l)) by (case: (l) Hl0 => [x | | ] //= Hl0 ; apply f_equal ; field ; contradict Hl0 ; by apply f_equal).
apply (filterlim_ext_loc (fun x => (- / - x))).
case: l Hl {Hl0} => [l| |] //= Hl.
apply Ropp_0_gt_lt_contravar in Hl.
exists (mkposreal _ Hl) => /= x H.
field ; apply Rlt_not_eq.
rewrite /ball /= /AbsRing_ball /abs /minus /plus /opp /= in H.
apply Rabs_lt_between' in H.
apply Rlt_le_trans with (1 := proj2 H), Req_le.
apply Rplus_opp_r.
exists 0 => x H.
field ; by apply Rlt_not_eq.
eapply filterlim_comp.
2: apply filterlim_Rbar_opp.
eapply filterlim_comp.
apply filterlim_Rbar_opp.
apply Hw.
apply Rbar_opp_lt.
rewrite Rbar_opp_involutive /= Ropp_0 ; by apply Hl.
contradict Hl0.
rewrite -(Rbar_opp_involutive l) Hl0 /= ; apply f_equal ; ring.
case: l => [l| |] //= Hl _.
assert (H1: 0 < l / 2).
apply Rdiv_lt_0_compat with (1 := Hl).
apply Rlt_R0_R2.
intros P [eps HP].
suff He : 0 < Rmin (eps * ((l / 2) * l)) (l / 2).
exists (mkposreal _ He) => x /= Hx.
apply HP.
assert (H2: l / 2 < x).
apply Rle_lt_trans with (l - l / 2).
apply Req_le ; field.
apply Rabs_lt_between'.
apply Rlt_le_trans with (1 := Hx).
apply Rmin_r.
assert (H3: 0 < x).
now apply Rlt_trans with (l / 2).
rewrite /ball /= /AbsRing_ball /abs /minus /plus /opp /=.
replace (/ x + - / l) with (- (x - l) / (x * l)).
rewrite Rabs_div.
rewrite Rabs_Ropp.
apply Rlt_div_l.
apply Rabs_pos_lt, Rgt_not_eq.
now apply Rmult_lt_0_compat.
apply Rlt_le_trans with (eps * ((l / 2) * l)).
apply Rlt_le_trans with (1 := Hx).
apply Rmin_l.
apply Rmult_le_compat_l.
apply Rlt_le, eps.
rewrite Rabs_mult.
rewrite (Rabs_pos_eq l).
apply Rmult_le_compat_r.
now apply Rlt_le.
apply Rle_trans with (2 := Rle_abs _).
now apply Rlt_le.
now apply Rlt_le.
apply Rgt_not_eq.
now apply Rmult_lt_0_compat.
field ; split ; apply Rgt_not_eq => //.
apply Rmin_case.
apply Rmult_lt_0_compat.
apply cond_pos.
now apply Rmult_lt_0_compat.
exact H1.
intros P [eps HP].
exists (/eps) => n Hn.
apply HP.
rewrite /ball /= /AbsRing_ball /abs /minus /plus /opp /=.
rewrite Ropp_0 Rplus_0_r Rabs_Rinv.
rewrite -(Rinv_involutive eps).
apply Rinv_lt_contravar.
apply Rmult_lt_0_compat.
apply Rinv_0_lt_compat, eps.
apply Rabs_pos_lt, Rgt_not_eq, Rlt_trans with (/eps).
apply Rinv_0_lt_compat, eps.
exact Hn.
apply Rlt_le_trans with (2 := Rle_abs _).
exact Hn.
apply Rgt_not_eq, eps.
apply Rgt_not_eq, Rlt_trans with (/eps).
apply Rinv_0_lt_compat, eps.
exact Hn.
