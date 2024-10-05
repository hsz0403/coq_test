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

Lemma ex_lim_seq_const (a : R) : ex_lim_seq (fun n => a).
Proof.
Admitted.

Lemma Lim_seq_const (a : R) : Lim_seq (fun n => a) = a.
Proof.
intros.
apply is_lim_seq_unique.
Admitted.

Lemma eventually_subseq_loc : forall phi, eventually (fun n => (phi n < phi (S n))%nat) -> filterlim phi eventually eventually.
Proof.
intros phi [M Hphi] P [N HP].
exists (N+M)%nat.
intros n Hn.
apply HP.
apply plus_le_reg_l with M.
rewrite Arith.Plus.plus_comm ; apply le_trans with (1:=Hn).
apply le_trans with (1:=le_plus_r (phi M) _).
assert (H:(forall x, M+phi M + x <= M+phi (x+M))%nat).
induction x as [|x IH].
rewrite plus_0_l plus_0_r.
apply le_refl.
rewrite <- plus_n_Sm.
apply lt_le_S.
apply le_lt_trans with (1:=IH).
apply plus_lt_compat_l.
apply Hphi.
apply le_plus_r.
assert (M <= n)%nat.
apply le_trans with (2:=Hn); apply le_plus_r.
specialize (H (n-M)%nat).
replace (n-M+M)%nat with n in H.
apply le_trans with (2:=H).
rewrite (Arith.Plus.plus_comm _ (phi M)) -Arith.Plus.plus_assoc.
apply plus_le_compat_l.
rewrite le_plus_minus_r.
apply le_refl.
exact H0.
rewrite Arith.Plus.plus_comm.
Admitted.

Lemma eventually_subseq : forall phi, (forall n, (phi n < phi (S n))%nat) -> filterlim phi eventually eventually.
Proof.
intros phi Hphi.
apply eventually_subseq_loc.
Admitted.

Lemma is_lim_seq_subseq (u : nat -> R) (l : Rbar) (phi : nat -> nat) : filterlim phi eventually eventually -> is_lim_seq u l -> is_lim_seq (fun n => u (phi n)) l.
Proof.
intros Hphi.
Admitted.

Lemma ex_lim_seq_subseq (u : nat -> R) (phi : nat -> nat) : filterlim phi eventually eventually -> ex_lim_seq u -> ex_lim_seq (fun n => u (phi n)).
Proof.
move => Hphi [l Hu].
exists l.
Admitted.

Lemma Lim_seq_subseq (u : nat -> R) (phi : nat -> nat) : filterlim phi eventually eventually -> ex_lim_seq u -> Lim_seq (fun n => u (phi n)) = Lim_seq u.
Proof.
move => Hphi Hu.
apply is_lim_seq_unique.
apply is_lim_seq_subseq.
exact Hphi.
Admitted.

Lemma is_lim_seq_incr_1 (u : nat -> R) (l : Rbar) : is_lim_seq u l <-> is_lim_seq (fun n => u (S n)) l.
Proof.
split ; intros H P HP ; destruct (H P HP) as [N HN].
-
exists N.
intros n Hn.
apply HN.
now apply le_S.
-
exists (S N).
intros n Hn.
destruct n as [|n] ; try easy.
apply HN.
Admitted.

Lemma ex_lim_seq_incr_1 (u : nat -> R) : ex_lim_seq u <-> ex_lim_seq (fun n => u (S n)).
Proof.
split ; move => [l H] ; exists l.
by apply -> is_lim_seq_incr_1.
Admitted.

Lemma Lim_seq_incr_1 (u : nat -> R) : Lim_seq (fun n => u (S n)) = Lim_seq u.
Proof.
rewrite /Lim_seq.
replace (LimSup_seq (fun n : nat => u (S n))) with (LimSup_seq u).
replace (LimInf_seq (fun n : nat => u (S n))) with (LimInf_seq u).
by [].
rewrite /LimInf_seq ; case: ex_LimInf_seq => l1 H1 ; case: ex_LimInf_seq => l2 H2 /= ; case: l1 H1 => [l1 | | ] /= H1 ; case: l2 H2 => [l2 | | ] /= H2.
apply Rbar_finite_eq, Rle_antisym ; apply le_epsilon => e He ; set eps := mkposreal e He ; apply Rlt_le.
case: (proj2 (H1 (pos_div_2 eps))) => /= {H1} N H1.
case: (proj1 (H2 (pos_div_2 eps)) N) => /= {H2} n [Hn H2].
apply Rlt_trans with (u (S n) + e/2).
replace l1 with ((l1-e/2)+e/2) by ring.
apply Rplus_lt_compat_r.
apply H1.
apply le_trans with (1 := Hn).
apply le_n_Sn.
replace (l2+e) with ((l2+e/2)+e/2) by field.
by apply Rplus_lt_compat_r, H2.
case: (proj2 (H2 (pos_div_2 eps))) => /= {H2} N H2.
case: (proj1 (H1 (pos_div_2 eps)) (S N)) => /= {H1} .
case => [ | n] [Hn H1].
by apply le_Sn_0 in Hn.
apply Rlt_trans with (u (S n) + e/2).
replace l2 with ((l2-e/2)+e/2) by ring.
apply Rplus_lt_compat_r.
apply H2.
by apply le_S_n, Hn.
replace (l1+e) with ((l1+e/2)+e/2) by field.
by apply Rplus_lt_compat_r, H1.
have : False => //.
case: (H2 (l1+1)) => {H2} N /= H2.
case: (proj1 (H1 (mkposreal _ Rlt_0_1)) (S N)) ; case => /= {H1} [ | n] [Hn].
by apply le_Sn_0 in Hn.
apply Rle_not_lt, Rlt_le, H2.
by apply le_S_n.
have : False => //.
case: (proj2 (H1 (mkposreal _ Rlt_0_1))) => {H1} N /= H1.
case: ((H2 (l1-1)) N) => /= {H2} n [Hn].
apply Rle_not_lt, Rlt_le, H1.
by apply le_trans with (2 := le_n_Sn _).
have : False => //.
case: (H1 (l2+1)) => {H1} N /= H1.
case: (proj1 (H2 (mkposreal _ Rlt_0_1)) N) => /= {H2} n [Hn].
apply Rle_not_lt, Rlt_le, H1.
by apply le_trans with (2 := le_n_Sn _).
by [].
have : False => //.
case: (H1 0) => {H1} N H1.
case: (H2 0 N)=> {H2} n [Hn].
apply Rle_not_lt, Rlt_le, H1.
by apply le_trans with (2 := le_n_Sn _).
have : False => //.
case: (proj2 (H2 (mkposreal _ Rlt_0_1))) => /= {H2} N H2.
case: (H1 (l2-1) (S N)) ; case => [ | n] [Hn].
by apply le_Sn_0 in Hn.
by apply Rle_not_lt, Rlt_le, H2, le_S_n.
have : False => //.
case: (H2 0) => {H2} N H2.
case: (H1 0 (S N)) ; case => [ | n] [Hn].
by apply le_Sn_0 in Hn.
by apply Rle_not_lt, Rlt_le, H2, le_S_n.
by [].
rewrite /LimSup_seq ; case: ex_LimSup_seq => l1 H1 ; case: ex_LimSup_seq => l2 H2 /= ; case: l1 H1 => [l1 | | ] /= H1 ; case: l2 H2 => [l2 | | ] /= H2.
apply Rbar_finite_eq, Rle_antisym ; apply le_epsilon => e He ; set eps := mkposreal e He ; apply Rlt_le.
case: (proj2 (H2 (pos_div_2 eps))) => /= {H2} N H2.
case: ((proj1 (H1 (pos_div_2 eps))) (S N)) ; case => /= {H1} [ | n] [Hn H1].
by apply le_Sn_0 in Hn.
replace l1 with ((l1-e/2)+e/2) by ring.
replace (l2+e) with ((l2+e/2)+e/2) by field.
apply Rplus_lt_compat_r.
apply Rlt_trans with (1 := H1).
by apply H2, le_S_n.
case: (proj2 (H1 (pos_div_2 eps))) => /= {H1} N H1.
case: ((proj1 (H2 (pos_div_2 eps))) N) => /= {H2} n [Hn H2].
replace l2 with ((l2-e/2)+e/2) by ring.
replace (l1+e) with ((l1+e/2)+e/2) by field.
apply Rplus_lt_compat_r.
apply Rlt_trans with (1 := H2).
by apply H1, le_trans with (2 := le_n_Sn _).
have : False => //.
case: (proj2 (H1 (mkposreal _ Rlt_0_1))) => /= {H1} N H1.
case: (H2 (l1+1) N) => n [Hn].
by apply Rle_not_lt, Rlt_le, H1, le_trans with (2 := le_n_Sn _).
have : False => //.
case: (H2 (l1-1)) => {H2} N H2.
case: (proj1 (H1 (mkposreal _ Rlt_0_1)) (S N)) ; case => [ | n] [Hn] /= .
by apply le_Sn_0 in Hn.
by apply Rle_not_lt, Rlt_le, H2, le_S_n.
have : False => //.
case: (proj2 (H2 (mkposreal _ Rlt_0_1))) => {H2} /= N H2.
case: (H1 (l2+1) (S N)) ; case => [ | n] [Hn] /= .
by apply le_Sn_0 in Hn.
by apply Rle_not_lt, Rlt_le, H2, le_S_n.
by [].
have : False => //.
case: (H2 0) => {H2} N H2.
case: (H1 0 (S N)) ; case => [ | n] [Hn] /= .
by apply le_Sn_0 in Hn.
by apply Rle_not_lt, Rlt_le, H2, le_S_n.
have : False => //.
case: (H1 (l2-1)) => {H1} N H1.
case: (proj1 (H2 (mkposreal _ Rlt_0_1)) N) => /= {H2} n [Hn].
by apply Rle_not_lt, Rlt_le, H1, le_trans with (2 := le_n_Sn _).
have : False => //.
case: (H1 0) => {H1} N H1.
case: (H2 0 N) => {H2} n [Hn].
by apply Rle_not_lt, Rlt_le, H1, le_trans with (2 := le_n_Sn _).
Admitted.

Lemma is_lim_seq_incr_n (u : nat -> R) (N : nat) (l : Rbar) : is_lim_seq u l <-> is_lim_seq (fun n => u (n + N)%nat) l.
Proof.
split.
elim: N u => [ | N IH] u Hu.
move: Hu ; apply is_lim_seq_ext => n ; by rewrite plus_0_r.
apply is_lim_seq_incr_1, IH in Hu.
move: Hu ; by apply is_lim_seq_ext => n ; by rewrite plus_n_Sm.
elim: N u => [ | N IH] u Hu.
move: Hu ; apply is_lim_seq_ext => n ; by rewrite plus_0_r.
apply is_lim_seq_incr_1, IH.
Admitted.

Lemma ex_lim_seq_incr_n (u : nat -> R) (N : nat) : ex_lim_seq u <-> ex_lim_seq (fun n => u (n + N)%nat).
Proof.
split ; move => [l H] ; exists l.
by apply -> is_lim_seq_incr_n.
Admitted.

Lemma Lim_seq_incr_n (u : nat -> R) (N : nat) : Lim_seq (fun n => u (n + N)%nat) = Lim_seq u.
Proof.
elim: N u => [ | N IH] u.
apply Lim_seq_ext => n ; by rewrite plus_0_r.
rewrite -(Lim_seq_incr_1 u) -(IH (fun n => u (S n))).
Admitted.

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
Admitted.

Lemma ex_lim_seq_dec (u : nat -> R) : {ex_lim_seq u} + {~ex_lim_seq u}.
Proof.
case: (Rbar_eq_dec (LimSup_seq u) (LimInf_seq u)) => H.
left ; by apply ex_lim_LimSup_LimInf_seq.
right ; contradict H ; by apply ex_lim_LimSup_LimInf_seq.
