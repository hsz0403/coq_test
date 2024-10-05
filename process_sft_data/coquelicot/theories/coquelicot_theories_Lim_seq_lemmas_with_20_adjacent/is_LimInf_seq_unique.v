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

Lemma Inf_seq_scal_l (a : R) (u : nat -> Rbar) : 0 <= a -> Inf_seq (fun n => Rbar_mult a (u n)) = Rbar_mult a (Inf_seq u).
Proof.
move => Ha.
rewrite Inf_opp_sup.
rewrite -(Sup_seq_ext (fun n => Rbar_mult a (Rbar_opp (u n)))).
rewrite Sup_seq_scal_l.
by rewrite -Rbar_mult_opp_r -(Inf_opp_sup u).
by [].
Admitted.

Lemma is_sup_seq_le (u v : nat -> Rbar) {l1 l2 : Rbar} : (forall n, Rbar_le (u n) (v n)) -> (is_sup_seq u l1) -> (is_sup_seq v l2) -> Rbar_le l1 l2.
Proof.
Admitted.

Lemma is_inf_seq_le (u v : nat -> Rbar) {l1 l2 : Rbar} : (forall n, Rbar_le (u n) (v n)) -> (is_inf_seq u l1) -> (is_inf_seq v l2) -> Rbar_le l1 l2.
Proof.
Admitted.

Lemma Sup_seq_le (u v : nat -> Rbar) : (forall n, Rbar_le (u n) (v n)) -> Rbar_le (Sup_seq u) (Sup_seq v).
Proof.
intros Heq ; unfold Sup_seq ; case (ex_sup_seq u) ; intros l1 Hu ; case (ex_sup_seq v) ; simpl ; intros l2 Hv.
Admitted.

Lemma Inf_seq_le (u v : nat -> Rbar) : (forall n, Rbar_le (u n) (v n)) -> Rbar_le (Inf_seq u) (Inf_seq v).
Proof.
move => Heq ; rewrite /Inf_seq ; case: (ex_inf_seq u) => l1 Hu ; case: (ex_inf_seq v) => /= l2 Hv.
Admitted.

Lemma Inf_le_sup (u : nat -> Rbar) : Rbar_le (Inf_seq u) (Sup_seq u).
Proof.
rewrite /Inf_seq ; case: (ex_inf_seq _) ; case => [iu | | ] Hiu ; rewrite /Sup_seq ; case: (ex_sup_seq _) ; case => [su | | ] Hsu //=.
apply le_epsilon => e He ; set eps := mkposreal e He ; case: (Hiu (pos_div_2 eps)) => {Hiu} Hiu _ ; case: (Hsu (pos_div_2 eps)) => {Hsu} Hsu _ ; apply Rlt_le.
have : (iu = iu - e/2 + e/2) ; first by ring.
move => -> ; have : (su+e = su + e/2 + e/2) ; first by field.
by move => -> ; apply Rplus_lt_compat_r, (Rbar_lt_trans (Finite (iu - e/2)) (u O) (Finite (su + e/2))).
set eps := mkposreal _ Rlt_0_1 ; case: (Hiu eps) => {Hiu} Hiu _ ; move: (Hiu O) => {Hiu} ; apply Rbar_le_not_lt, Rbar_lt_le, Hsu.
set eps := mkposreal _ Rlt_0_1 ; case: (Hsu eps) => {Hsu} Hsu _ ; move: (Hsu O) => {Hsu} ; apply Rbar_le_not_lt, Rbar_lt_le, Hiu.
Admitted.

Lemma is_sup_seq_major (u : nat -> Rbar) (l : Rbar) (n : nat) : is_sup_seq u l -> Rbar_le (u n) l.
Proof.
case: l => [l | | ] //= Hl.
move: (fun eps => proj1 (Hl eps) n) => {Hl}.
case: (u n) => [un | | ] //= Hun.
apply le_epsilon => e He ; apply Rlt_le.
apply: Hun (mkposreal e He).
by move: (Hun (mkposreal _ Rlt_0_1)).
case: (u n) => [un | | ] //.
move: (Hl (u n) n) ; case: (u n) => [un | | ] //= {Hl} Hl.
Admitted.

Lemma Sup_seq_minor_lt (u : nat -> Rbar) (M : R) : Rbar_lt M (Sup_seq u) <-> exists n, Rbar_lt M (u n).
Proof.
rewrite /Sup_seq ; case: ex_sup_seq => l Hl ; simpl proj1_sig ; split => H.
case: l Hl H => [l | | ] Hl H.
apply Rminus_lt_0 in H.
case: (proj2 (Hl (mkposreal _ H))) ; simpl pos => {Hl} n Hl.
exists n.
replace M with (l - (l - M)) by ring.
by apply Hl.
apply (Hl M).
by [].
case: H => n Hn.
apply Rbar_lt_le_trans with (u n).
exact: Hn.
Admitted.

Lemma Sup_seq_minor_le (u : nat -> Rbar) (M : R) (n : nat) : Rbar_le M (u n) -> Rbar_le M (Sup_seq u).
Proof.
intros H'.
destruct (Rbar_le_lt_or_eq_dec _ _ H') as [H|H].
apply Rbar_lt_le.
apply Sup_seq_minor_lt.
by exists n.
rewrite H.
rewrite /Sup_seq ; case: ex_sup_seq => l Hl ; simpl proj1_sig.
Admitted.

Lemma is_LimInf_opp_LimSup_seq (u : nat -> R) (l : Rbar) : is_LimInf_seq (fun n => - u n) (Rbar_opp l) <-> is_LimSup_seq u l.
Proof.
case: l => [l | | ] /= ; split => Hl.
move => eps ; case: (Hl eps) => {Hl} H1 H2 ; split.
move => N ; case: (H1 N) => {H1} n [Hn H1].
exists n ; split.
by [].
apply Ropp_lt_cancel.
apply Rlt_le_trans with (1 := H1) ; right ; ring.
case: H2 => N H2.
exists N => n Hn.
apply Ropp_lt_cancel.
apply Rle_lt_trans with (2 := H2 _ Hn) ; right ; ring.
move => eps ; case: (Hl eps) => {Hl} H1 H2 ; split.
move => N ; case: (H1 N) => {H1} n [Hn H1].
exists n ; split.
by [].
apply Ropp_lt_cancel ; rewrite Ropp_involutive.
apply Rle_lt_trans with (2 := H1) ; right ; ring.
case: H2 => N H2.
exists N => n Hn.
apply Ropp_lt_cancel ; rewrite Ropp_involutive.
apply Rlt_le_trans with (1 := H2 _ Hn) ; right ; ring.
move => M N.
case: (Hl (-M) N) => {Hl} n [Hn Hl].
exists n ; split.
by [].
by apply Ropp_lt_cancel.
move => M N.
case: (Hl (-M) N) => {Hl} n [Hn Hl].
exists n ; split.
by [].
apply Ropp_lt_cancel ; by rewrite Ropp_involutive.
move => M.
case: (Hl (-M)) => {Hl} N Hl.
exists N => n Hn.
apply Ropp_lt_cancel.
by apply Hl.
move => M.
case: (Hl (-M)) => {Hl} N Hl.
exists N => n Hn.
apply Ropp_lt_cancel ; rewrite Ropp_involutive.
Admitted.

Lemma is_LimSup_opp_LimInf_seq (u : nat -> R) (l : Rbar) : is_LimSup_seq (fun n => - u n) (Rbar_opp l) <-> is_LimInf_seq u l.
Proof.
case: l => [l | | ] /= ; split => Hl.
move => eps ; case: (Hl eps) => {Hl} H1 H2 ; split.
move => N ; case: (H1 N) => {H1} n [Hn H1].
exists n ; split.
by [].
apply Ropp_lt_cancel.
apply Rle_lt_trans with (2 := H1) ; right ; ring.
case: H2 => N H2.
exists N => n Hn.
apply Ropp_lt_cancel.
apply Rlt_le_trans with (1 := H2 _ Hn) ; right ; ring.
move => eps ; case: (Hl eps) => {Hl} H1 H2 ; split.
move => N ; case: (H1 N) => {H1} n [Hn H1].
exists n ; split.
by [].
apply Ropp_lt_cancel ; rewrite Ropp_involutive.
apply Rlt_le_trans with (1 := H1) ; right ; ring.
case: H2 => N H2.
exists N => n Hn.
apply Ropp_lt_cancel ; rewrite Ropp_involutive.
apply Rle_lt_trans with (2 := H2 _ Hn) ; right ; ring.
move => M.
case: (Hl (-M)) => {Hl} N Hl.
exists N => n Hn.
apply Ropp_lt_cancel.
by apply Hl.
move => M.
case: (Hl (-M)) => {Hl} N Hl.
exists N => n Hn.
apply Ropp_lt_cancel ; rewrite Ropp_involutive.
by apply Hl.
move => M N.
case: (Hl (-M) N) => {Hl} n [Hn Hl].
exists n ; split.
by [].
by apply Ropp_lt_cancel.
move => M N.
case: (Hl (-M) N) => {Hl} n [Hn Hl].
exists n ; split.
by [].
Admitted.

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
Admitted.

Lemma is_LimInf_supInf_seq (u : nat -> R) (l : Rbar) : is_LimInf_seq u l <-> is_sup_seq (fun m => Inf_seq (fun n => u (n + m)%nat)) l.
Proof.
rewrite -is_LimSup_opp_LimInf_seq.
rewrite is_LimSup_infSup_seq.
rewrite -is_sup_opp_inf_seq.
rewrite Rbar_opp_involutive.
Admitted.

Lemma is_LimSup_seq_ext_loc (u v : nat -> R) (l : Rbar) : eventually (fun n => u n = v n) -> is_LimSup_seq u l -> is_LimSup_seq v l.
Proof.
case: l => [l | | ] /= [Next Hext] Hu.
move => eps.
case: (Hu eps) => {Hu} H1 H2 ; split.
move => N.
case: (H1 (N + Next)%nat) => {H1} n [Hn H1].
exists n ; rewrite -Hext ; intuition.
case: H2 => N H2.
exists (N + Next)%nat => n Hn.
rewrite -Hext ; intuition.
move => M N.
case: (Hu M (N + Next)%nat) => {Hu} n [Hn Hu].
exists n ; rewrite -Hext ; intuition.
move => M.
case: (Hu M) => {Hu} N Hu.
exists (N + Next)%nat => n Hn.
Admitted.

Lemma is_LimSup_seq_ext (u v : nat -> R) (l : Rbar) : (forall n, u n = v n) -> is_LimSup_seq u l -> is_LimSup_seq v l.
Proof.
move => Hext.
apply is_LimSup_seq_ext_loc.
Admitted.

Lemma is_LimInf_seq_ext_loc (u v : nat -> R) (l : Rbar) : eventually (fun n => u n = v n) -> is_LimInf_seq u l -> is_LimInf_seq v l.
Proof.
case => N Hext Hu.
apply is_LimSup_opp_LimInf_seq.
apply is_LimSup_seq_ext_loc with (fun n => - u n).
exists N => n Hn ; by rewrite Hext.
Admitted.

Lemma is_LimInf_seq_ext (u v : nat -> R) (l : Rbar) : (forall n, u n = v n) -> is_LimInf_seq u l -> is_LimInf_seq v l.
Proof.
move => Hext.
apply is_LimInf_seq_ext_loc.
Admitted.

Lemma ex_LimSup_seq (u : nat -> R) : {l : Rbar | is_LimSup_seq u l}.
Proof.
case: (ex_inf_seq (fun m : nat => Sup_seq (fun n : nat => u (n + m)%nat))) => l Hl.
exists l.
Admitted.

Lemma ex_LimInf_seq (u : nat -> R) : {l : Rbar | is_LimInf_seq u l}.
Proof.
case: (ex_sup_seq (fun m : nat => Inf_seq (fun n : nat => u (n + m)%nat))) => l Hl.
exists l.
Admitted.

Lemma is_LimSup_seq_unique (u : nat -> R) (l : Rbar) : is_LimSup_seq u l -> LimSup_seq u = l.
Proof.
move => H.
rewrite /LimSup_seq.
case: ex_LimSup_seq => lu Hu /=.
apply is_LimSup_infSup_seq in H.
apply is_LimSup_infSup_seq in Hu.
rewrite -(is_inf_seq_unique _ _ Hu).
Admitted.

Lemma LimSup_InfSup_seq (u : nat -> R) : LimSup_seq u = Inf_seq (fun m => Sup_seq (fun n => u (n + m)%nat)).
Proof.
apply is_LimSup_seq_unique.
apply is_LimSup_infSup_seq.
rewrite /Inf_seq.
Admitted.

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

Lemma is_LimInf_seq_unique (u : nat -> R) (l : Rbar) : is_LimInf_seq u l -> LimInf_seq u = l.
Proof.
move => H.
rewrite /LimInf_seq.
case: ex_LimInf_seq => lu Hu /=.
apply is_LimInf_supInf_seq in H.
apply is_LimInf_supInf_seq in Hu.
rewrite -(is_sup_seq_unique _ _ Hu).
by apply is_sup_seq_unique.
