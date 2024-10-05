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

Lemma filterlim_le : forall {T F} {FF : ProperFilter' F} (f g : T -> R) (lf lg : Rbar), F (fun x => f x <= g x) -> filterlim f F (Rbar_locally lf) -> filterlim g F (Rbar_locally lg) -> Rbar_le lf lg.
Proof.
intros T F FF f g lf lg H Hf Hg.
apply Rbar_not_lt_le.
intros Hl.
apply filter_not_empty.
destruct lf as [lf| |] ; destruct lg as [lg| |] ; try easy.
-
assert (Hl' : 0 < (lf - lg) / 2).
apply Rdiv_lt_0_compat.
now apply -> Rminus_lt_0.
apply Rlt_R0_R2.
assert (Hlf : locally lf (fun y => (lf + lg) / 2 < y)).
apply open_gt.
replace ((lf + lg) / 2) with (lf - (lf - lg) / 2) by field.
apply Rabs_lt_between'.
by rewrite /Rminus Rplus_opp_r Rabs_R0.
assert (Hlg : locally lg (fun y => y < (lf + lg) / 2)).
apply open_lt.
replace ((lf + lg) / 2) with (lg + (lf - lg) / 2) by field.
apply Rabs_lt_between'.
by rewrite /Rminus Rplus_opp_r Rabs_R0.
specialize (Hf _ Hlf).
specialize (Hg _ Hlg).
unfold filtermap in Hf, Hg.
generalize (filter_and _ _ (filter_and _ _ Hf Hg) H).
apply filter_imp.
intros x [[H1 H2] H3].
apply Rle_not_lt with (1 := H3).
now apply Rlt_trans with ((lf + lg) / 2).
-
assert (Hlf : locally lf (fun y => lf - 1 < y)).
apply open_gt.
apply Rabs_lt_between'.
rewrite /Rminus Rplus_opp_r Rabs_R0.
apply Rlt_0_1.
assert (Hlg : Rbar_locally m_infty (fun y => Rbar_lt y (lf - 1))).
now apply open_Rbar_lt'.
specialize (Hf _ Hlf).
specialize (Hg _ Hlg).
unfold filtermap in Hf, Hg.
generalize (filter_and _ _ (filter_and _ _ Hf Hg) H).
apply filter_imp.
intros x [[H1 H2] H3].
apply Rle_not_lt with (1 := H3).
now apply Rlt_trans with (lf - 1).
-
assert (Hlf : Rbar_locally p_infty (fun y => Rbar_lt (lg + 1) y)).
now apply open_Rbar_gt'.
assert (Hlg : locally lg (fun y => y < lg + 1)).
apply open_lt.
apply Rabs_lt_between'.
rewrite /Rminus Rplus_opp_r Rabs_R0.
apply Rlt_0_1.
specialize (Hf _ Hlf).
specialize (Hg _ Hlg).
unfold filtermap in Hf, Hg.
generalize (filter_and _ _ (filter_and _ _ Hf Hg) H).
apply filter_imp.
intros x [[H1 H2] H3].
apply Rle_not_lt with (1 := H3).
now apply Rlt_trans with (lg + 1).
-
assert (Hlf : Rbar_locally p_infty (fun y => Rbar_lt 0 y)).
now apply open_Rbar_gt'.
assert (Hlg : Rbar_locally m_infty (fun y => Rbar_lt y 0)).
now apply open_Rbar_lt'.
specialize (Hf _ Hlf).
specialize (Hg _ Hlg).
unfold filtermap in Hf, Hg.
generalize (filter_and _ _ (filter_and _ _ Hf Hg) H).
apply filter_imp.
intros x [[H1 H2] H3].
apply Rle_not_lt with (1 := H3).
now apply Rlt_trans with 0.
