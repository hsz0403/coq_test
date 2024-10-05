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
contradict H ; by apply H.
