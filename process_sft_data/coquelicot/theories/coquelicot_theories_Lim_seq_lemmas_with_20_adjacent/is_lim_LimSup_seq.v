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

Lemma LimInf_SupInf_seq (u : nat -> R) : LimInf_seq u = Sup_seq (fun m => Inf_seq (fun n => u (n + m)%nat)).
Proof.
apply is_LimInf_seq_unique.
apply is_LimInf_supInf_seq.
rewrite /Sup_seq.
Admitted.

Lemma is_LimSup_LimInf_seq_le (u : nat -> R) (ls li : Rbar) : is_LimSup_seq u ls -> is_LimInf_seq u li -> Rbar_le li ls.
Proof.
case: ls => [ls | | ] ; case: li => [li | | ] //= Hls Hli.
apply le_epsilon => e He ; set eps := pos_div_2 (mkposreal e He).
replace li with ((li - eps) + eps) by ring.
replace (ls + e) with ((ls + eps) + eps) by (simpl ; field).
apply Rplus_le_compat_r, Rlt_le.
case: (proj2 (Hls eps)) => {Hls} Ns Hls.
case: (proj2 (Hli eps)) => {Hli} Ni Hli.
apply Rlt_trans with (u (Ns + Ni)%nat).
apply Hli ; by intuition.
apply Hls ; by intuition.
case: (proj2 (Hls (mkposreal _ Rlt_0_1))) => {Hls} /= Ns Hls.
case: (Hli (ls + 1)) => {Hli} Ni Hli.
absurd (ls + 1 < u (Ns + Ni)%nat).
apply Rle_not_lt, Rlt_le, Hls ; by intuition.
apply Hli ; by intuition.
case: (proj2 (Hli (mkposreal _ Rlt_0_1))) => {Hli} /= Ni Hli.
case: (Hls (li - 1)) => {Hls} Ns Hls.
absurd (li - 1 < u (Ns + Ni)%nat).
apply Rle_not_lt, Rlt_le, Hls ; by intuition.
apply Hli ; by intuition.
case: (Hli 0) => {Hli} /= Ni Hli.
case: (Hls 0) => {Hls} Ns Hls.
absurd (0 < u (Ns + Ni)%nat).
apply Rle_not_lt, Rlt_le, Hls ; by intuition.
Admitted.

Lemma LimSup_LimInf_seq_le (u : nat -> R) : Rbar_le (LimInf_seq u) (LimSup_seq u).
Proof.
rewrite /LimInf_seq ; case: ex_LimInf_seq => /= li Hli.
rewrite /LimSup_seq ; case: ex_LimSup_seq => /= ls Hls.
Admitted.

Lemma is_LimSup_seq_const (a : R) : is_LimSup_seq (fun _ => a) a.
Proof.
intros eps ; split.
intros N ; exists N ; split.
by apply le_refl.
apply Rminus_lt_0 ; ring_simplify.
by apply eps.
exists O => _ _.
apply Rminus_lt_0 ; ring_simplify.
Admitted.

Lemma LimSup_seq_const (a : R) : LimSup_seq (fun _ => a) = a.
Proof.
apply is_LimSup_seq_unique.
Admitted.

Lemma is_LimInf_seq_const (a : R) : is_LimInf_seq (fun _ => a) a.
Proof.
intros eps ; split.
intros N ; exists N ; split.
by apply le_refl.
apply Rminus_lt_0 ; ring_simplify.
by apply eps.
exists O => _ _.
apply Rminus_lt_0 ; ring_simplify.
Admitted.

Lemma LimInf_seq_const (a : R) : LimInf_seq (fun _ => a) = a.
Proof.
apply is_LimInf_seq_unique.
Admitted.

Lemma LimSup_seq_opp (u : nat -> R) : LimSup_seq (fun n => - u n) = Rbar_opp (LimInf_seq u).
Proof.
rewrite LimSup_InfSup_seq LimInf_SupInf_seq.
rewrite Inf_opp_sup ; apply f_equal, Sup_seq_ext => m.
Admitted.

Lemma LimInf_seq_opp (u : nat -> R) : LimInf_seq (fun n => - u n) = Rbar_opp (LimSup_seq u).
Proof.
rewrite LimSup_InfSup_seq LimInf_SupInf_seq.
rewrite Sup_opp_inf ; apply f_equal, Inf_seq_ext => m.
Admitted.

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
Admitted.

Lemma LimInf_le (u v : nat -> R) : eventually (fun n => u n <= v n) -> Rbar_le (LimInf_seq u) (LimInf_seq v).
Proof.
intros.
apply Rbar_opp_le.
rewrite -!LimSup_seq_opp.
apply LimSup_le.
move: H ; apply filter_imp => n.
Admitted.

Lemma is_LimSup_seq_scal_pos (a : R) (u : nat -> R) (l : Rbar) : (0 < a) -> is_LimSup_seq u l -> is_LimSup_seq (fun n => a * u n) (Rbar_mult a l).
Proof.
case: l => [l | | ] /= Ha Hu.
move => eps.
suff He : 0 < eps / a.
case: (Hu (mkposreal _ He)) => {Hu} /= H1 H2 ; split.
move => N ; case: (H1 N) => {H1} n [Hn H1].
exists n ; split.
by [].
rewrite (Rmult_comm _ (u n)) ; apply Rlt_div_l.
by [].
apply Rle_lt_trans with (2 := H1) ; right ; field ; by apply Rgt_not_eq.
case: H2 => N H2.
exists N => n Hn.
rewrite (Rmult_comm _ (u n)) ; apply Rlt_div_r.
by [].
apply Rlt_le_trans with (1 := H2 _ Hn) ; right ; field ; by apply Rgt_not_eq.
apply Rdiv_lt_0_compat ; [ by case eps | by [] ].
case: Rle_dec (Rlt_le _ _ Ha) => // H _.
case: Rle_lt_or_eq_dec (Rlt_not_eq _ _ Ha) => {H} // _ _.
move => M N.
case: (Hu (M / a) N) => {Hu} n [Hn Hu].
exists n ; split.
by [].
rewrite (Rmult_comm _ (u n)) ; apply Rlt_div_l.
by [].
by [].
case: Rle_dec (Rlt_le _ _ Ha) => // H _.
case: Rle_lt_or_eq_dec (Rlt_not_eq _ _ Ha) => {H} // _ _.
move => M.
case: (Hu (M / a)) => {Hu} N Hu.
exists N => n Hn.
rewrite (Rmult_comm _ (u n)) ; apply Rlt_div_r.
by [].
Admitted.

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

Lemma ex_finite_lim_seq_correct (u : nat -> R) : ex_finite_lim_seq u <-> ex_lim_seq u /\ is_finite (Lim_seq u).
Proof.
split.
case => l Hl.
split.
by exists l.
by rewrite (is_lim_seq_unique _ _ Hl).
case ; case => l Hl H.
exists l.
rewrite -(is_lim_seq_unique _ _ Hl).
Admitted.

Lemma ex_lim_seq_dec (u : nat -> R) : {ex_lim_seq u} + {~ex_lim_seq u}.
Proof.
case: (Rbar_eq_dec (LimSup_seq u) (LimInf_seq u)) => H.
left ; by apply ex_lim_LimSup_LimInf_seq.
Admitted.

Lemma ex_finite_lim_seq_dec (u : nat -> R) : {ex_finite_lim_seq u} + {~ ex_finite_lim_seq u}.
Proof.
case: (ex_lim_seq_dec u) => H.
apply Lim_seq_correct in H.
case: (Lim_seq u) H => [l | | ] H.
left ; by exists l.
right ; rewrite ex_finite_lim_seq_correct.
rewrite (is_lim_seq_unique _ _ H) /is_finite //= ; by case.
right ; rewrite ex_finite_lim_seq_correct.
rewrite (is_lim_seq_unique _ _ H) /is_finite //= ; by case.
right ; rewrite ex_finite_lim_seq_correct.
Admitted.

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
Admitted.

Lemma is_lim_seq_INR : is_lim_seq INR p_infty.
Proof.
apply is_lim_seq_spec.
move => M.
suff Hm : 0 <= Rmax 0 M.
exists (S (nfloor (Rmax 0 M) Hm)) => n Hn.
apply Rlt_le_trans with (2 := le_INR _ _ Hn).
rewrite /nfloor S_INR.
case: nfloor_ex => {n Hn} /= n Hn.
apply Rle_lt_trans with (1 := Rmax_r 0 M).
by apply Hn.
Admitted.

Lemma ex_lim_seq_INR : ex_lim_seq INR.
Proof.
Admitted.

Lemma Lim_seq_INR : Lim_seq INR = p_infty.
Proof.
intros.
apply is_lim_seq_unique.
Admitted.

Lemma is_lim_seq_const (a : R) : is_lim_seq (fun n => a) a.
Proof.
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
by [].
