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

Lemma Rbar_is_glb_inf_seq (u : nat -> Rbar) (l : Rbar) : Rbar_is_glb (fun x => exists n, x = u n) l -> is_inf_seq u l.
Proof.
move => H ; apply is_sup_opp_inf_seq ; apply Rbar_is_lub_sup_seq ; apply Rbar_glb_lub.
Admitted.

Lemma is_sup_seq_ext (u v : nat -> Rbar) (l : Rbar) : (forall n, u n = v n) -> is_sup_seq u l -> is_sup_seq v l.
Proof.
case: l => [l | | ] Heq ; rewrite /is_sup_seq => Hu.
move => eps ; case: (Hu eps) => {Hu} Hu1 Hu2 ; split.
move => n ; by rewrite -Heq.
case: Hu2 => n Hu2 ; exists n ; by rewrite -Heq.
move => M ; case: (Hu M) => {Hu} n Hu ; exists n ; by rewrite -Heq.
Admitted.

Lemma is_inf_seq_ext (u v : nat -> Rbar) (l : Rbar) : (forall n, u n = v n) -> is_inf_seq u l -> is_inf_seq v l.
Proof.
case: l => [l | | ] Heq ; rewrite /is_inf_seq => Hu.
move => eps ; case: (Hu eps) => {Hu} Hu1 Hu2 ; split.
move => n ; by rewrite -Heq.
case: Hu2 => n Hu2 ; exists n ; by rewrite -Heq.
move => M n ; by rewrite -Heq.
Admitted.

Lemma ex_sup_seq (u : nat -> Rbar) : {l : Rbar | is_sup_seq u l}.
Proof.
case (LPO (fun n => p_infty = u n)) => [/= | [np Hnp] | Hnp].
intro n0 ; destruct (u n0) as [r | | ].
now right.
left ; auto.
now right.
exists p_infty => M.
exists np ; by rewrite -Hnp.
case (Rbar_ex_lub (fun x => exists n, x = u n)).
Admitted.

Lemma ex_inf_seq (u : nat -> Rbar) : {l : Rbar | is_inf_seq u l}.
Proof.
case : (ex_sup_seq (fun n => Rbar_opp (u n))) => l Hl.
Admitted.

Lemma is_sup_seq_unique (u : nat -> Rbar) (l : Rbar) : is_sup_seq u l -> Sup_seq u = l.
Proof.
move => Hl ; rewrite /Sup_seq ; case: (ex_sup_seq _) => l0 Hl0 /= ; case: l Hl => [l | | ] Hl ; case: l0 Hl0 => [l0 | | ] Hl0 //.
apply Rbar_finite_eq, Rle_antisym ; apply le_epsilon => e He ; set eps := mkposreal e He ; apply Rlt_le ; case: (Hl (pos_div_2 eps)) => {Hl} Hl [n Hn] ; case: (Hl0 (pos_div_2 eps)) => {Hl0} Hl0 [n0 Hn0].
have: (l0 = (l0 - eps/2) + eps/2) ; [by field | move => -> ] ; have : (l + e = (l + eps/2) + eps/2) ; [ simpl ; field | move => -> ] ; apply Rplus_lt_compat_r, (Rbar_lt_trans (Finite (l0 - eps/2)) (u n0) (Finite (l + eps/2)) Hn0 (Hl _)).
have: (l = (l - eps/2) + eps/2) ; [by field | move => -> ] ; have : (l0 + e = (l0 + eps/2) + eps/2) ; [ simpl ; field | move => -> ] ; apply Rplus_lt_compat_r, (Rbar_lt_trans (Finite (l - eps/2)) (u n) (Finite (l0 + eps/2)) Hn (Hl0 _)).
case: (Hl0 (l + 1)) => n {Hl0} Hl0 ; contradict Hl0 ; apply Rbar_le_not_lt, Rbar_lt_le, (Hl (mkposreal _ Rlt_0_1)).
case: (Hl (mkposreal _ Rlt_0_1)) => {Hl} _ [n Hl] ; contradict Hl ; apply Rbar_le_not_lt, Rbar_lt_le, Hl0.
case: (Hl (l0 + 1)) => n {Hl} Hl ; contradict Hl ; apply Rbar_le_not_lt, Rbar_lt_le, (Hl0 (mkposreal _ Rlt_0_1)).
case: (Hl 0) => n {Hl} Hl ; contradict Hl ; apply Rbar_le_not_lt, Rbar_lt_le, Hl0.
case: (Hl0 (mkposreal _ Rlt_0_1)) => {Hl0} _ [n Hl0] ; contradict Hl0 ; apply Rbar_le_not_lt, Rbar_lt_le, Hl.
Admitted.

Lemma Sup_seq_correct (u : nat -> Rbar) : is_sup_seq u (Sup_seq u).
Proof.
Admitted.

Lemma is_inf_seq_unique (u : nat -> Rbar) (l : Rbar) : is_inf_seq u l -> Inf_seq u = l.
Proof.
move => Hl ; rewrite /Inf_seq ; case: (ex_inf_seq _) => l0 Hl0 /= ; case: l Hl => [l | | ] Hl ; case: l0 Hl0 => [l0 | | ] Hl0 //.
apply Rbar_finite_eq, Rle_antisym ; apply le_epsilon => e He ; set eps := mkposreal e He ; apply Rlt_le ; case: (Hl (pos_div_2 eps)) => {Hl} Hl [n Hn] ; case: (Hl0 (pos_div_2 eps)) => {Hl0} Hl0 [n0 Hn0].
have: (l0 = (l0 - eps/2) + eps/2) ; [by field | move => -> ] ; have : (l + e = (l + eps/2) + eps/2) ; [ simpl ; field | move => -> ] ; apply Rplus_lt_compat_r, (Rbar_lt_trans (Finite (l0 - eps/2)) (u n) (Finite (l + eps/2)) (Hl0 _) Hn).
have: (l = (l - eps/2) + eps/2) ; [by field | move => -> ] ; have : (l0 + e = (l0 + eps/2) + eps/2) ; [ simpl ; field | move => -> ] ; apply Rplus_lt_compat_r, (Rbar_lt_trans (Finite (l - eps/2)) (u n0) (Finite (l0 + eps/2)) (Hl _) Hn0).
case: (Hl (mkposreal _ Rlt_0_1)) => {Hl} _ [n Hl] ; contradict Hl ; apply Rbar_le_not_lt, Rbar_lt_le, Hl0.
case: (Hl0 (l - 1)) => n {Hl0} Hl0 ; contradict Hl0 ; apply Rbar_le_not_lt, Rbar_lt_le, (Hl (mkposreal _ Rlt_0_1)).
case: (Hl0 (mkposreal _ Rlt_0_1)) => {Hl0} _ [n Hl0] ; contradict Hl0 ; apply Rbar_le_not_lt, Rbar_lt_le, Hl.
case: (Hl0 0) => n {Hl0} Hl0 ; contradict Hl0 ; apply Rbar_le_not_lt, Rbar_lt_le, Hl.
case: (Hl (l0 - 1)) => n {Hl} Hl ; contradict Hl ; apply Rbar_le_not_lt, Rbar_lt_le, (Hl0 (mkposreal _ Rlt_0_1)).
Admitted.

Lemma Inf_seq_correct (u : nat -> Rbar) : is_inf_seq u (Inf_seq u).
Proof.
Admitted.

Lemma Sup_seq_ext (u v : nat -> Rbar) : (forall n, (u n) = (v n)) -> Sup_seq u = Sup_seq v.
Proof.
intro Heq ; rewrite {2}/Sup_seq ; case (ex_sup_seq v) ; simpl ; intros l2 Hv.
Admitted.

Lemma Rbar_sup_eq_lub (u : nat -> Rbar) : Sup_seq u = Rbar_lub (fun x => exists n, x = u n).
Proof.
rewrite /Sup_seq ; case: (ex_sup_seq _) => /= s Hs.
rewrite /Rbar_lub ; case: (Rbar_ex_lub _) => /= l Hl.
Admitted.

Lemma Inf_eq_glb (u : nat -> Rbar) : Inf_seq u = Rbar_glb (fun x => exists n, x = u n).
Proof.
rewrite /Inf_seq ; case: (ex_inf_seq _) => /= s Hs.
rewrite /Rbar_glb ; case: (Rbar_ex_glb _) => /= l Hl.
Admitted.

Lemma Sup_opp_inf (u : nat -> Rbar) : Sup_seq u = Rbar_opp (Inf_seq (fun n => Rbar_opp (u n))).
Proof.
rewrite /Inf_seq ; case: (ex_inf_seq _) => iu Hiu /=.
apply is_sup_seq_unique.
apply is_inf_opp_sup_seq.
Admitted.

Lemma Inf_opp_sup (u : nat -> Rbar) : Inf_seq u = Rbar_opp (Sup_seq (fun n => Rbar_opp (u n))).
Proof.
rewrite Sup_opp_inf Rbar_opp_involutive.
rewrite /Inf_seq.
repeat (case: ex_inf_seq ; intros) => /=.
apply is_inf_seq_glb in p.
apply is_inf_seq_glb in p0.
move: p p0 ; apply Rbar_is_glb_eq.
Admitted.

Lemma Sup_seq_scal_l (a : R) (u : nat -> Rbar) : 0 <= a -> Sup_seq (fun n => Rbar_mult a (u n)) = Rbar_mult a (Sup_seq u).
Proof.
case => Ha.
rewrite /Sup_seq.
case: ex_sup_seq => al Hau.
case: ex_sup_seq => l Hu.
simpl proj1_sig.
apply Rbar_le_antisym.
apply is_sup_seq_lub in Hau.
apply is_sup_seq_lub in Hu.
apply Hau => _ [n ->].
suff : Rbar_le (u n) l.
case: (u n) => [un | | ] ; case: (l) => [l' | | ] /= ; try (by case) ; try (case: Rle_dec (Rlt_le _ _ Ha) => //= Ha' _ ; case: Rle_lt_or_eq_dec (Rlt_not_eq _ _ Ha) => //= _ _ _ ; by left).
intros H ; apply Rmult_le_compat_l => // ; by apply Rlt_le.
apply Hu.
by exists n.
suff : Rbar_le l (Rbar_div_pos al (mkposreal a Ha)).
case: (al) => [al' | | ] ; case: (l) => [l' | | ] /= ; try (by case) ; try (case: Rle_dec (Rlt_le _ _ Ha) => //= Ha' _ ; case: Rle_lt_or_eq_dec (Rlt_not_eq _ _ Ha) => //= _ _ _ ; by left).
intros H ; rewrite Rmult_comm ; apply Rle_div_r => //.
apply is_sup_seq_lub in Hau.
apply is_sup_seq_lub in Hu.
apply Hu => _ [n ->].
suff : Rbar_le (Rbar_mult a (u n)) al.
case: (u n) => [un | | ] ; case: (al) => [al' | | ] /= ; try (by case) ; try (case: Rle_dec (Rlt_le _ _ Ha) => //= Ha' _ ; case: Rle_lt_or_eq_dec (Rlt_not_eq _ _ Ha) => //= _ _ ; try (by case) ; by left).
intros H ; rewrite Rmult_comm in H ; apply Rle_div_r => //.
apply Hau.
by exists n.
rewrite -Ha.
transitivity (Sup_seq (fun _ => 0)).
apply Sup_seq_ext.
move => n ; case: (u n) => [un | | ] /=.
apply f_equal ; ring.
case: Rle_dec (Rle_refl 0) => //= H _.
case: Rle_lt_or_eq_dec (Rle_not_lt _ _ H) => //= H _.
case: Rle_dec (Rle_refl 0) => //= H _.
case: Rle_lt_or_eq_dec (Rle_not_lt _ _ H) => //= H _.
transitivity 0.
apply is_sup_seq_unique.
move => eps ; split => /=.
move => _ ; ring_simplify ; by apply eps.
exists 0%nat ; apply Rminus_lt_0 ; ring_simplify ; by apply eps.
case: (Sup_seq u) => [l | | ] /=.
apply f_equal ; ring.
case: Rle_dec (Rle_refl 0) => //= H _.
case: Rle_lt_or_eq_dec (Rle_not_lt _ _ H) => //= H _.
case: Rle_dec (Rle_refl 0) => //= H _.
Admitted.

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

Lemma Inf_seq_ext (u v : nat -> Rbar) : (forall n, (u n) = (v n)) -> Inf_seq u = Inf_seq v.
Proof.
intro Heq ; rewrite {2}/Inf_seq ; case (ex_inf_seq v) ; simpl ; intros l2 Hv.
by apply (is_inf_seq_unique u), is_inf_seq_ext with v.
