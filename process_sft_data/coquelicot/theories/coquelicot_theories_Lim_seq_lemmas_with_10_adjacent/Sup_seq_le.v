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

Lemma Sup_seq_ext (u v : nat -> Rbar) : (forall n, (u n) = (v n)) -> Sup_seq u = Sup_seq v.
Proof.
intro Heq ; rewrite {2}/Sup_seq ; case (ex_sup_seq v) ; simpl ; intros l2 Hv.
Admitted.

Lemma Inf_seq_ext (u v : nat -> Rbar) : (forall n, (u n) = (v n)) -> Inf_seq u = Inf_seq v.
Proof.
intro Heq ; rewrite {2}/Inf_seq ; case (ex_inf_seq v) ; simpl ; intros l2 Hv.
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

Lemma Sup_seq_le (u v : nat -> Rbar) : (forall n, Rbar_le (u n) (v n)) -> Rbar_le (Sup_seq u) (Sup_seq v).
Proof.
intros Heq ; unfold Sup_seq ; case (ex_sup_seq u) ; intros l1 Hu ; case (ex_sup_seq v) ; simpl ; intros l2 Hv.
apply (is_sup_seq_le u v) ; auto.
