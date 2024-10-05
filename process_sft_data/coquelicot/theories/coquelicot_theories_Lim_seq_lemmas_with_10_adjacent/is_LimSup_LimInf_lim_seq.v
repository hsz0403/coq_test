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

Lemma is_LimInf_seq_scal_pos (a : R) (u : nat -> R) (l : Rbar) : (0 < a) -> is_LimInf_seq u l -> is_LimInf_seq (fun n => a * u n) (Rbar_mult a l).
Proof.
move => Ha Hu.
apply is_LimSup_opp_LimInf_seq in Hu.
apply is_LimSup_opp_LimInf_seq.
replace (Rbar_opp (Rbar_mult a l)) with (Rbar_mult a (Rbar_opp l)).
apply is_LimSup_seq_ext with (fun n => a * - u n).
move => n ; ring.
by apply is_LimSup_seq_scal_pos.
case: (l) => [x | | ] /=.
apply f_equal ; ring.
case: Rle_dec (Rlt_le _ _ Ha) => // H _.
case: Rle_lt_or_eq_dec (Rlt_not_eq _ _ Ha) => // H _.
case: Rle_dec (Rlt_le _ _ Ha) => // H _.
Admitted.

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
Admitted.

Lemma is_LimInf_seq_ind_1 (u : nat -> R) (l : Rbar) : is_LimInf_seq u l <-> is_LimInf_seq (fun n => u (S n)) l.
Proof.
rewrite -?is_LimSup_opp_LimInf_seq.
Admitted.

Lemma is_LimSup_seq_ind_k (u : nat -> R) (k : nat) (l : Rbar) : is_LimSup_seq u l <-> is_LimSup_seq (fun n => u (n + k)%nat) l.
Proof.
elim: k u => [ | k IH] /= u.
split ; apply is_LimSup_seq_ext => n ; by rewrite -plus_n_O.
rewrite is_LimSup_seq_ind_1.
rewrite (IH (fun n => u (S n))).
Admitted.

Lemma is_LimInf_seq_ind_k (u : nat -> R) (k : nat) (l : Rbar) : is_LimInf_seq u l <-> is_LimInf_seq (fun n => u (n + k)%nat) l.
Proof.
rewrite -?is_LimSup_opp_LimInf_seq.
Admitted.

Lemma is_lim_seq_spec : forall u l, is_lim_seq' u l <-> is_lim_seq u l.
Proof.
destruct l as [l| |] ; split.
-
intros H P [eps LP].
destruct (H eps) as [N HN].
exists N => n Hn.
apply LP.
now apply HN.
-
intros LP eps.
specialize (LP (fun y => Rabs (y - l) < eps)).
apply LP.
now exists eps.
-
intros H P [M LP].
destruct (H M) as [N HN].
exists N => n Hn.
apply LP.
now apply HN.
-
intros LP M.
specialize (LP (fun y => M < y)).
apply LP.
now exists M.
-
intros H P [M LP].
destruct (H M) as [N HN].
exists N => n Hn.
apply LP.
now apply HN.
-
intros LP M.
specialize (LP (fun y => y < M)).
apply LP.
Admitted.

Lemma is_lim_seq_Reals (u : nat -> R) (l : R) : is_lim_seq u l <-> Un_cv u l.
Proof.
split => Hl.
move => e He.
apply (Hl (fun y => R_dist y l < e)).
now exists (mkposreal _ He).
unfold is_lim_seq.
change (Rbar_locally l) with (locally l).
apply (filterlim_locally u l).
case => e He.
case: (Hl e He) => {Hl} /= N Hl.
exists N => n Hn.
Admitted.

Lemma is_lim_seq_p_infty_Reals (u : nat -> R) : is_lim_seq u p_infty <-> cv_infty u.
Proof.
split => Hl.
move => M.
case: (Hl (fun x => M < x)) => {Hl} [ | N Hl].
by exists M.
by exists N.
move => P [M HP].
eapply filter_imp.
by apply HP.
case: (Hl M) => {Hl} N HN.
Admitted.

Lemma is_lim_LimSup_seq (u : nat -> R) (l : Rbar) : is_lim_seq u l -> is_LimSup_seq u l.
Proof.
move /is_lim_seq_spec.
case: l => [l | | ] /= Hu.
move => eps ; case: (Hu eps) => {Hu} N Hu ; split.
move => N0.
exists (N + N0)%nat ; split.
by apply le_plus_r.
by apply Rabs_lt_between', Hu, le_plus_l.
exists N => n Hn.
by apply Rabs_lt_between', Hu.
move => M N0.
case: (Hu M) => {Hu} N Hu.
exists (N + N0)%nat ; split.
by apply le_plus_r.
by apply Hu, le_plus_l.
Admitted.

Lemma is_lim_LimInf_seq (u : nat -> R) (l : Rbar) : is_lim_seq u l -> is_LimInf_seq u l.
Proof.
move /is_lim_seq_spec.
case: l => [l | | ] /= Hu.
move => eps ; case: (Hu eps) => {Hu} N Hu ; split.
move => N0.
exists (N + N0)%nat ; split.
by apply le_plus_r.
by apply Rabs_lt_between', Hu, le_plus_l.
exists N => n Hn.
by apply Rabs_lt_between', Hu.
by [].
move => M N0.
case: (Hu M) => {Hu} N Hu.
exists (N + N0)%nat ; split.
by apply le_plus_r.
Admitted.

Lemma ex_lim_LimSup_LimInf_seq (u : nat -> R) : ex_lim_seq u <-> LimSup_seq u = LimInf_seq u.
Proof.
split => Hl.
case: Hl => l Hu.
transitivity l.
apply is_LimSup_seq_unique.
by apply is_lim_LimSup_seq.
apply sym_eq, is_LimInf_seq_unique.
by apply is_lim_LimInf_seq.
exists (LimSup_seq u).
apply is_LimSup_LimInf_lim_seq.
rewrite /LimSup_seq ; by case: ex_LimSup_seq.
Admitted.

Lemma is_lim_seq_ext_loc (u v : nat -> R) (l : Rbar) : eventually (fun n => u n = v n) -> is_lim_seq u l -> is_lim_seq v l.
Proof.
Admitted.

Lemma ex_lim_seq_ext_loc (u v : nat -> R) : eventually (fun n => u n = v n) -> ex_lim_seq u -> ex_lim_seq v.
Proof.
move => H [l H0].
Admitted.

Lemma Lim_seq_ext_loc (u v : nat -> R) : eventually (fun n => u n = v n) -> Lim_seq u = Lim_seq v.
Proof.
intros.
rewrite /Lim_seq.
apply (f_equal (fun x => Rbar_div_pos x _)).
apply f_equal2 ; apply sym_eq.
apply is_LimSup_seq_unique.
apply is_LimSup_seq_ext_loc with u.
by [].
rewrite /LimSup_seq ; by case: ex_LimSup_seq.
apply is_LimInf_seq_unique.
apply is_LimInf_seq_ext_loc with u.
by [].
Admitted.

Lemma is_lim_seq_ext (u v : nat -> R) (l : Rbar) : (forall n, u n = v n) -> is_lim_seq u l -> is_lim_seq v l.
Proof.
move => Hext.
apply is_lim_seq_ext_loc.
Admitted.

Lemma ex_lim_seq_ext (u v : nat -> R) : (forall n, u n = v n) -> ex_lim_seq u -> ex_lim_seq v.
Proof.
move => H [l H0].
Admitted.

Lemma Lim_seq_ext (u v : nat -> R) : (forall n, u n = v n) -> Lim_seq u = Lim_seq v.
Proof.
move => Hext.
apply Lim_seq_ext_loc.
Admitted.

Lemma is_lim_seq_unique (u : nat -> R) (l : Rbar) : is_lim_seq u l -> Lim_seq u = l.
Proof.
move => Hu.
rewrite /Lim_seq.
replace l with (Rbar_div_pos (Rbar_plus l l) {| pos := 2; cond_pos := Rlt_R0_R2 |}) by (case: (l) => [x | | ] //= ; apply f_equal ; field).
apply (f_equal (fun x => Rbar_div_pos x _)).
apply f_equal2.
apply is_LimSup_seq_unique.
by apply is_lim_LimSup_seq.
apply is_LimInf_seq_unique.
Admitted.

Lemma Lim_seq_correct (u : nat -> R) : ex_lim_seq u -> is_lim_seq u (Lim_seq u).
Proof.
intros (l,H).
cut (Lim_seq u = l).
intros ; rewrite H0 ; apply H.
Admitted.

Lemma Lim_seq_correct' (u : nat -> R) : ex_finite_lim_seq u -> is_lim_seq u (real (Lim_seq u)).
Proof.
intros (l,H).
cut (real (Lim_seq u) = l).
intros ; rewrite H0 ; apply H.
replace l with (real l) by auto.
Admitted.

Lemma is_LimSup_LimInf_lim_seq (u : nat -> R) (l : Rbar) : is_LimSup_seq u l -> is_LimInf_seq u l -> is_lim_seq u l.
Proof.
case: l => [l | | ] /= Hs Hi ; apply is_lim_seq_spec.
move => eps.
case: (proj2 (Hs eps)) => {Hs} Ns Hs.
case: (proj2 (Hi eps)) => {Hi} Ni Hi.
exists (Ns + Ni)%nat => n Hn.
apply Rabs_lt_between' ; split.
apply Hi ; intuition.
apply Hs ; intuition.
exact Hi.
exact Hs.
