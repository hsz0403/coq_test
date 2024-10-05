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

Lemma is_LimInf_seq_unique (u : nat -> R) (l : Rbar) : is_LimInf_seq u l -> LimInf_seq u = l.
Proof.
move => H.
rewrite /LimInf_seq.
case: ex_LimInf_seq => lu Hu /=.
apply is_LimInf_supInf_seq in H.
apply is_LimInf_supInf_seq in Hu.
rewrite -(is_sup_seq_unique _ _ Hu).
Admitted.

Lemma LimSup_InfSup_seq (u : nat -> R) : LimSup_seq u = Inf_seq (fun m => Sup_seq (fun n => u (n + m)%nat)).
Proof.
apply is_LimSup_seq_unique.
apply is_LimSup_infSup_seq.
rewrite /Inf_seq.
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

Lemma LimInf_SupInf_seq (u : nat -> R) : LimInf_seq u = Sup_seq (fun m => Inf_seq (fun n => u (n + m)%nat)).
Proof.
apply is_LimInf_seq_unique.
apply is_LimInf_supInf_seq.
rewrite /Sup_seq.
by case: ex_sup_seq.
