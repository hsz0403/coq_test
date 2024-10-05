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

Lemma is_lim_seq_le_loc (u v : nat -> R) (l1 l2 : Rbar) : eventually (fun n => u n <= v n) -> is_lim_seq u l1 -> is_lim_seq v l2 -> Rbar_le l1 l2.
Proof.
Admitted.

Lemma Lim_seq_le_loc (u v : nat -> R) : eventually (fun n => u n <= v n) -> Rbar_le (Lim_seq u) (Lim_seq v).
Proof.
intros.
move: (LimSup_le _ _ H) (LimInf_le _ _ H).
move: (LimSup_LimInf_seq_le u) (LimSup_LimInf_seq_le v).
unfold Lim_seq.
case: (LimSup_seq u) => [lsu | | ] //= ; case: (LimInf_seq u) => [liu | | ] //= ; case: (LimSup_seq v) => [lsv | | ] //= ; case: (LimInf_seq v) => [liv | | ] //= ; intros.
apply Rmult_le_compat_r.
apply Rlt_le, Rinv_0_lt_compat, Rlt_0_2.
by apply Rplus_le_compat.
Admitted.

Lemma is_lim_seq_le (u v : nat -> R) (l1 l2 : Rbar) : (forall n, u n <= v n) -> is_lim_seq u l1 -> is_lim_seq v l2 -> Rbar_le l1 l2.
Proof.
intros H.
apply filterlim_le.
Admitted.

Lemma filterlim_ge_p_infty : forall {T F} {FF : Filter F} (f g : T -> R), F (fun x => f x <= g x) -> filterlim f F (Rbar_locally p_infty) -> filterlim g F (Rbar_locally p_infty).
Proof.
intros T F FF f g H Hf.
intros P [M HM].
assert (H' : Rbar_locally p_infty (fun y => M < y)).
now exists M.
unfold filtermap.
generalize (filter_and (fun x : T => f x <= g x) _ H (Hf (fun y : R => M < y) H')).
apply filter_imp.
intros x [H1 H2].
apply HM.
Admitted.

Lemma filterlim_le_m_infty : forall {T F} {FF : Filter F} (f g : T -> R), F (fun x => g x <= f x) -> filterlim f F (Rbar_locally m_infty) -> filterlim g F (Rbar_locally m_infty).
Proof.
intros T F FF f g H Hf.
intros P [M HM].
pose ineq (y : R) := y < M.
assert (H' : Rbar_locally m_infty ineq).
now exists M.
unfold filtermap.
generalize (filter_and _ (fun x : T => ineq (f x)) H (Hf ineq H')).
apply filter_imp.
intros x [H1 H2].
apply HM.
Admitted.

Lemma filterlim_le_le : forall {T F} {FF : Filter F} (f g h : T -> R) (l : Rbar), F (fun x => f x <= g x <= h x) -> filterlim f F (Rbar_locally l) -> filterlim h F (Rbar_locally l) -> filterlim g F (Rbar_locally l).
Proof.
intros T F FF f g h l H Hf Hh.
destruct l as [l| |].
-
intros P [eps He].
assert (H' : Rbar_locally l (fun y => Rabs (y - l) < eps)).
now exists eps.
unfold filterlim, filter_le, filtermap in Hf, Hh |- *.
generalize (filter_and _ _ H (filter_and _ _ (Hf _ H') (Hh _ H'))).
apply filter_imp.
intros x [H1 [H2 H3]].
apply He.
apply Rabs_lt_between'.
split.
apply Rlt_le_trans with (2 := proj1 H1).
now apply Rabs_lt_between'.
apply Rle_lt_trans with (1 := proj2 H1).
now apply Rabs_lt_between'.
-
apply filterlim_ge_p_infty with (2 := Hf).
apply: filter_imp H.
now intros x [H _].
-
apply filterlim_le_m_infty with (2 := Hh).
apply: filter_imp H.
Admitted.

Lemma is_lim_seq_le_le_loc (u v w : nat -> R) (l : Rbar) : eventually (fun n => u n <= v n <= w n) -> is_lim_seq u l -> is_lim_seq w l -> is_lim_seq v l.
Proof.
Admitted.

Lemma is_lim_seq_le_le (u v w : nat -> R) (l : Rbar) : (forall n, u n <= v n <= w n) -> is_lim_seq u l -> is_lim_seq w l -> is_lim_seq v l.
Proof.
intros H.
apply filterlim_le_le.
Admitted.

Lemma is_lim_seq_le_p_loc (u v : nat -> R) : eventually (fun n => u n <= v n) -> is_lim_seq u p_infty -> is_lim_seq v p_infty.
Proof.
Admitted.

Lemma is_lim_seq_le_m_loc (u v : nat -> R) : eventually (fun n => v n <= u n) -> is_lim_seq u m_infty -> is_lim_seq v m_infty.
Proof.
Admitted.

Lemma is_lim_seq_decr_compare (u : nat -> R) (l : R) : is_lim_seq u l -> (forall n, (u (S n)) <= (u n)) -> forall n, l <= u n.
Proof.
move /is_lim_seq_spec => Hu H n.
apply Rnot_lt_le => H0.
apply Rminus_lt_0 in H0.
case: (Hu (mkposreal _ H0)) => {Hu} /= Nu Hu.
move: (Hu _ (le_plus_r n Nu)).
apply Rle_not_lt.
apply Rle_trans with (2 := Rabs_maj2 _).
rewrite Ropp_minus_distr'.
apply Rplus_le_compat_l.
apply Ropp_le_contravar.
elim: (Nu) => [ | m IH].
rewrite plus_0_r ; by apply Rle_refl.
rewrite -plus_n_Sm.
apply Rle_trans with (2 := IH).
Admitted.

Lemma is_lim_seq_incr_compare (u : nat -> R) (l : R) : is_lim_seq u l -> (forall n, (u n) <= (u (S n))) -> forall n, u n <= l.
Proof.
move /is_lim_seq_spec => Hu H n.
apply Rnot_lt_le => H0.
apply Rminus_lt_0 in H0.
case: (Hu (mkposreal _ H0)) => {Hu} /= Nu Hu.
move: (Hu _ (le_plus_r n Nu)).
apply Rle_not_lt.
apply Rle_trans with (2 := Rle_abs _).
apply Rplus_le_compat_r.
elim: (Nu) => [ | m IH].
rewrite plus_0_r ; by apply Rle_refl.
rewrite -plus_n_Sm.
apply Rle_trans with (1 := IH).
Admitted.

Lemma ex_lim_seq_decr (u : nat -> R) : (forall n, (u (S n)) <= (u n)) -> ex_lim_seq u.
Proof.
move => H.
exists (Inf_seq u).
apply is_lim_seq_spec.
rewrite /Inf_seq ; case: ex_inf_seq ; case => [l | | ] //= Hl.
move => eps ; case: (Hl eps) => Hl1 [N Hl2].
exists N => n Hn.
apply Rabs_lt_between' ; split.
by apply Hl1.
apply Rle_lt_trans with (2 := Hl2).
elim: n N {Hl2} Hn => [ | n IH] N Hn.
rewrite (le_n_O_eq _ Hn).
apply Rle_refl.
apply le_lt_eq_dec in Hn.
case: Hn => [Hn | ->].
apply Rle_trans with (1 := H _), IH ; intuition.
by apply Rle_refl.
move => M ; exists O => n _ ; by apply Hl.
move => M.
case: (Hl M) => {Hl} N Hl.
exists N => n Hn.
apply Rle_lt_trans with (2 := Hl).
elim: Hn => [ | {n} n Hn IH].
by apply Rle_refl.
apply Rle_trans with (2 := IH).
Admitted.

Lemma ex_lim_seq_incr (u : nat -> R) : (forall n, (u n) <= (u (S n))) -> ex_lim_seq u.
Proof.
move => H.
exists (Sup_seq u).
apply is_lim_seq_spec.
rewrite /Sup_seq ; case: ex_sup_seq ; case => [l | | ] //= Hl.
move => eps ; case: (Hl eps) => Hl1 [N Hl2].
exists N => n Hn.
apply Rabs_lt_between' ; split.
apply Rlt_le_trans with (1 := Hl2).
elim: Hn => [ | {n} n Hn IH].
by apply Rle_refl.
apply Rle_trans with (1 := IH).
by apply H.
by apply Hl1.
move => M.
case: (Hl M) => {Hl} N Hl.
exists N => n Hn.
apply Rlt_le_trans with (1 := Hl).
elim: Hn => [ | {n} n Hn IH].
by apply Rle_refl.
apply Rle_trans with (1 := IH).
by apply H.
Admitted.

Lemma ex_finite_lim_seq_decr (u : nat -> R) (M : R) : (forall n, (u (S n)) <= (u n)) -> (forall n, M <= u n) -> ex_finite_lim_seq u.
Proof.
intros.
apply ex_finite_lim_seq_correct.
have H1 : ex_lim_seq u.
exists (real (Inf_seq u)).
apply is_lim_seq_spec.
rewrite /Inf_seq ; case: ex_inf_seq ; case => [l | | ] //= Hl.
move => eps ; case: (Hl eps) => Hl1 [N Hl2].
exists N => n Hn.
apply Rabs_lt_between' ; split.
by apply Hl1.
apply Rle_lt_trans with (2 := Hl2).
elim: n N {Hl2} Hn => [ | n IH] N Hn.
rewrite (le_n_O_eq _ Hn).
apply Rle_refl.
apply le_lt_eq_dec in Hn.
case: Hn => [Hn | ->].
apply Rle_trans with (1 := H _), IH ; intuition.
by apply Rle_refl.
move: (Hl (u O) O) => H1 ; by apply Rlt_irrefl in H1.
case: (Hl M) => {Hl} n Hl.
apply Rlt_not_le in Hl.
by move: (Hl (H0 n)).
split => //.
apply Lim_seq_correct in H1.
case: (Lim_seq u) H1 => [l | | ] /= Hu.
by [].
apply is_lim_seq_spec in Hu.
case: (Hu (u O)) => {Hu} N Hu.
move: (Hu N (le_refl _)) => {Hu} Hu.
contradict Hu ; apply Rle_not_lt.
elim: N => [ | N IH].
by apply Rle_refl.
by apply Rle_trans with (1 := H _).
apply is_lim_seq_spec in Hu.
case: (Hu M) => {Hu} N Hu.
move: (Hu N (le_refl _)) => {Hu} Hu.
Admitted.

Lemma ex_finite_lim_seq_incr (u : nat -> R) (M : R) : (forall n, (u n) <= (u (S n))) -> (forall n, u n <= M) -> ex_finite_lim_seq u.
Proof.
intros.
case: (ex_finite_lim_seq_decr (fun n => - u n) (- M)).
move => n ; by apply Ropp_le_contravar.
move => n ; by apply Ropp_le_contravar.
move => l ; move => Hu.
exists (- l).
apply is_lim_seq_spec in Hu.
apply is_lim_seq_spec.
intros eps.
case: (Hu eps) => {Hu} N Hu.
exists N => n Hn.
replace (u n - - l) with (-(- u n - l)) by ring.
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
by [].
