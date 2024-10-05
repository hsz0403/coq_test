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

Lemma filterlim_Rbar_opp : forall x, filterlim Ropp (Rbar_locally x) (Rbar_locally (Rbar_opp x)).
Proof.
intros [x| |] P [eps He].
-
exists eps.
intros y Hy.
apply He.
rewrite /ball /= /AbsRing_ball /abs /minus /plus /opp /=.
by rewrite Ropp_involutive Rplus_comm Rabs_minus_sym.
-
exists (-eps).
intros y Hy.
apply He.
apply Ropp_lt_cancel.
by rewrite Ropp_involutive.
-
exists (-eps).
intros y Hy.
apply He.
apply Ropp_lt_cancel.
Admitted.

Lemma is_lim_seq_opp (u : nat -> R) (l : Rbar) : is_lim_seq u l <-> is_lim_seq (fun n => -u n) (Rbar_opp l).
Proof.
split ; move => Hu.
apply is_LimSup_LimInf_lim_seq.
apply is_LimSup_opp_LimInf_seq.
by apply is_lim_LimInf_seq.
apply is_LimInf_opp_LimSup_seq.
by apply is_lim_LimSup_seq.
apply is_LimSup_LimInf_lim_seq.
apply is_LimInf_opp_LimSup_seq.
by apply is_lim_LimInf_seq.
apply is_LimSup_opp_LimInf_seq.
Admitted.

Lemma ex_lim_seq_opp (u : nat -> R) : ex_lim_seq u <-> ex_lim_seq (fun n => -u n).
Proof.
split ; case => l Hl ; exists (Rbar_opp l).
by apply -> is_lim_seq_opp.
apply is_lim_seq_ext with (fun n => - - u n).
move => n ; by apply Ropp_involutive.
Admitted.

Lemma Lim_seq_opp (u : nat -> R) : Lim_seq (fun n => - u n) = Rbar_opp (Lim_seq u).
Proof.
rewrite /Lim_seq.
rewrite LimSup_seq_opp LimInf_seq_opp.
Admitted.

Lemma filterlim_Rbar_plus : forall x y z, is_Rbar_plus x y z -> filterlim (fun z => fst z + snd z) (filter_prod (Rbar_locally x) (Rbar_locally y)) (Rbar_locally z).
Proof.
intros x y z.
wlog: x y z / (Rbar_le 0 z).
intros Hw.
case: (Rbar_le_lt_dec 0 z) => Hz Hp.
by apply Hw.
apply (filterlim_ext (fun z => - (- fst z + - snd z))).
intros t.
ring.
rewrite -(Rbar_opp_involutive z).
eapply filterlim_comp.
2: apply filterlim_Rbar_opp.
assert (Hw' : filterlim (fun z => fst z + snd z) (filter_prod (Rbar_locally (Rbar_opp x)) (Rbar_locally (Rbar_opp y))) (Rbar_locally (Rbar_opp z))).
apply Hw.
rewrite -Ropp_0 -/(Rbar_opp 0).
apply <- Rbar_opp_le.
now apply Rbar_lt_le.
revert Hp.
clear.
destruct x as [x| |] ; destruct y as [y| |] ; destruct z as [z| |] => //=.
unfold is_Rbar_plus ; simpl => H.
injection H => <-.
apply f_equal, f_equal ; ring.
clear Hw.
intros P HP.
specialize (Hw' P HP).
destruct Hw' as [Q R H1 H2 H3].
exists (fun x => Q (- x)) (fun x => R (- x)).
now apply filterlim_Rbar_opp.
now apply filterlim_Rbar_opp.
intros u v HQ HR.
exact (H3 _ _ HQ HR).
unfold is_Rbar_plus.
case: z => [z| |] Hz Hp ; try by case: Hz.
case: x y Hp Hz => [x| |] ; case => [y| |] //= ; case => <- Hz.
intros P [eps He].
exists (fun u => Rabs (u - x) < pos_div_2 eps) (fun v => Rabs (v - y) < pos_div_2 eps).
now exists (pos_div_2 eps).
now exists (pos_div_2 eps).
intros u v Hu Hv.
apply He.
rewrite /ball /= /AbsRing_ball /abs /minus /plus /opp /=.
replace (u + v + - (x + y)) with ((u - x) + (v - y)) by ring.
rewrite (double_var eps) ; apply Rle_lt_trans with (1 := Rabs_triang _ _), Rplus_lt_compat.
now apply Hu.
now apply Hv.
wlog: x y Hp {Hz} / (is_finite x) => [Hw|Hx].
case: x y Hp {Hz} => [x| |] ; case => [y| |] // _.
now apply (Hw x p_infty).
assert (Hw': filterlim (fun z => fst z + snd z) (filter_prod (Rbar_locally y) (Rbar_locally p_infty)) (Rbar_locally p_infty)).
exact: Hw.
intros P HP.
specialize (Hw' P HP).
destruct Hw' as [Q R H1 H2 H3].
exists R Q ; try assumption.
intros u v Hu Hv.
rewrite Rplus_comm.
now apply (H3 v u).
clear Hw.
intros P [N HN].
exists (fun x => N/2 < x) (fun x => N/2 < x).
now exists (N/2).
now exists (N/2).
intros x y Hx Hy.
simpl.
apply HN.
rewrite (double_var N).
now apply Rplus_lt_compat.
case: x y Hp Hx => [x| |] ; case => [y| | ] //= _ _.
intros P [N HN].
exists (fun u => Rabs (u - x) < 1) (fun v => N - x + 1 < v).
now exists (mkposreal _ Rlt_0_1).
now exists (N - x + 1).
intros u v Hu Hv.
simpl.
apply HN.
replace N with (x - 1 + (N - x + 1)) by ring.
apply Rplus_lt_compat.
now apply Rabs_lt_between'.
Admitted.

Lemma is_lim_seq_plus (u v : nat -> R) (l1 l2 l : Rbar) : is_lim_seq u l1 -> is_lim_seq v l2 -> is_Rbar_plus l1 l2 l -> is_lim_seq (fun n => u n + v n) l.
Proof.
intros Hu Hv Hl.
eapply filterlim_comp_2 ; try eassumption.
Admitted.

Lemma is_lim_seq_plus' (u v : nat -> R) (l1 l2 : R) : is_lim_seq u l1 -> is_lim_seq v l2 -> is_lim_seq (fun n => u n + v n) (l1 + l2).
Proof.
intros Hu Hv.
eapply is_lim_seq_plus.
by apply Hu.
by apply Hv.
Admitted.

Lemma ex_lim_seq_plus (u v : nat -> R) : ex_lim_seq u -> ex_lim_seq v -> ex_Rbar_plus (Lim_seq u) (Lim_seq v) -> ex_lim_seq (fun n => u n + v n).
Proof.
intros [lu Hu] [lv Hv] Hl ; exists (Rbar_plus lu lv).
apply is_lim_seq_plus with lu lv ; try assumption.
rewrite -(is_lim_seq_unique u lu) //.
rewrite -(is_lim_seq_unique v lv) //.
Admitted.

Lemma Lim_seq_plus (u v : nat -> R) : ex_lim_seq u -> ex_lim_seq v -> ex_Rbar_plus (Lim_seq u) (Lim_seq v) -> Lim_seq (fun n => u n + v n) = Rbar_plus (Lim_seq u) (Lim_seq v).
Proof.
intros Hu Hv Hl.
apply is_lim_seq_unique.
eapply is_lim_seq_plus ; try apply Lim_seq_correct ; try assumption.
Admitted.

Lemma is_lim_seq_minus (u v : nat -> R) (l1 l2 l : Rbar) : is_lim_seq u l1 -> is_lim_seq v l2 -> is_Rbar_minus l1 l2 l -> is_lim_seq (fun n => u n - v n) l.
Proof.
intros H1 H2 Hl.
eapply is_lim_seq_plus ; try eassumption.
Admitted.

Lemma is_lim_seq_minus' (u v : nat -> R) (l1 l2 : R) : is_lim_seq u l1 -> is_lim_seq v l2 -> is_lim_seq (fun n => u n - v n) (l1 - l2).
Proof.
intros Hu Hv.
eapply is_lim_seq_minus ; try eassumption.
Admitted.

Lemma ex_lim_seq_minus (u v : nat -> R) : ex_lim_seq u -> ex_lim_seq v -> ex_Rbar_minus (Lim_seq u) (Lim_seq v) -> ex_lim_seq (fun n => u n - v n).
Proof.
intros [lu Hu] [lv Hv] Hl ; exists (Rbar_minus lu lv).
eapply is_lim_seq_minus ; try eassumption.
rewrite -(is_lim_seq_unique u lu) //.
rewrite -(is_lim_seq_unique v lv) //.
Admitted.

Lemma Lim_seq_minus (u v : nat -> R) : ex_lim_seq u -> ex_lim_seq v -> ex_Rbar_minus (Lim_seq u) (Lim_seq v) -> Lim_seq (fun n => u n - v n) = Rbar_minus (Lim_seq u) (Lim_seq v).
Proof.
intros Hu Hv Hl.
apply is_lim_seq_unique.
eapply is_lim_seq_minus ; try apply Lim_seq_correct ; try assumption.
Admitted.

Lemma filterlim_Rbar_inv : forall l : Rbar, l <> 0 -> filterlim Rinv (Rbar_locally l) (Rbar_locally (Rbar_inv l)).
Proof.
intros l.
wlog: l / (Rbar_lt 0 l).
intros Hw.
case: (Rbar_lt_le_dec 0 l) => Hl.
by apply Hw.
case: (Rbar_le_lt_or_eq_dec _ _ Hl) => // {Hl} Hl Hl0.
rewrite -(Rbar_opp_involutive (Rbar_inv l)).
replace (Rbar_opp (Rbar_inv l)) with (Rbar_inv (Rbar_opp l)) by (case: (l) Hl0 => [x | | ] //= Hl0 ; apply f_equal ; field ; contradict Hl0 ; by apply f_equal).
apply (filterlim_ext_loc (fun x => (- / - x))).
case: l Hl {Hl0} => [l| |] //= Hl.
apply Ropp_0_gt_lt_contravar in Hl.
exists (mkposreal _ Hl) => /= x H.
field ; apply Rlt_not_eq.
rewrite /ball /= /AbsRing_ball /abs /minus /plus /opp /= in H.
apply Rabs_lt_between' in H.
apply Rlt_le_trans with (1 := proj2 H), Req_le.
apply Rplus_opp_r.
exists 0 => x H.
field ; by apply Rlt_not_eq.
eapply filterlim_comp.
2: apply filterlim_Rbar_opp.
eapply filterlim_comp.
apply filterlim_Rbar_opp.
apply Hw.
apply Rbar_opp_lt.
rewrite Rbar_opp_involutive /= Ropp_0 ; by apply Hl.
contradict Hl0.
rewrite -(Rbar_opp_involutive l) Hl0 /= ; apply f_equal ; ring.
case: l => [l| |] //= Hl _.
assert (H1: 0 < l / 2).
apply Rdiv_lt_0_compat with (1 := Hl).
apply Rlt_R0_R2.
intros P [eps HP].
suff He : 0 < Rmin (eps * ((l / 2) * l)) (l / 2).
exists (mkposreal _ He) => x /= Hx.
apply HP.
assert (H2: l / 2 < x).
apply Rle_lt_trans with (l - l / 2).
apply Req_le ; field.
apply Rabs_lt_between'.
apply Rlt_le_trans with (1 := Hx).
apply Rmin_r.
assert (H3: 0 < x).
now apply Rlt_trans with (l / 2).
rewrite /ball /= /AbsRing_ball /abs /minus /plus /opp /=.
replace (/ x + - / l) with (- (x - l) / (x * l)).
rewrite Rabs_div.
rewrite Rabs_Ropp.
apply Rlt_div_l.
apply Rabs_pos_lt, Rgt_not_eq.
now apply Rmult_lt_0_compat.
apply Rlt_le_trans with (eps * ((l / 2) * l)).
apply Rlt_le_trans with (1 := Hx).
apply Rmin_l.
apply Rmult_le_compat_l.
apply Rlt_le, eps.
rewrite Rabs_mult.
rewrite (Rabs_pos_eq l).
apply Rmult_le_compat_r.
now apply Rlt_le.
apply Rle_trans with (2 := Rle_abs _).
now apply Rlt_le.
now apply Rlt_le.
apply Rgt_not_eq.
now apply Rmult_lt_0_compat.
field ; split ; apply Rgt_not_eq => //.
apply Rmin_case.
apply Rmult_lt_0_compat.
apply cond_pos.
now apply Rmult_lt_0_compat.
exact H1.
intros P [eps HP].
exists (/eps) => n Hn.
apply HP.
rewrite /ball /= /AbsRing_ball /abs /minus /plus /opp /=.
rewrite Ropp_0 Rplus_0_r Rabs_Rinv.
rewrite -(Rinv_involutive eps).
apply Rinv_lt_contravar.
apply Rmult_lt_0_compat.
apply Rinv_0_lt_compat, eps.
apply Rabs_pos_lt, Rgt_not_eq, Rlt_trans with (/eps).
apply Rinv_0_lt_compat, eps.
exact Hn.
apply Rlt_le_trans with (2 := Rle_abs _).
exact Hn.
apply Rgt_not_eq, eps.
apply Rgt_not_eq, Rlt_trans with (/eps).
apply Rinv_0_lt_compat, eps.
Admitted.

Lemma is_lim_seq_inv (u : nat -> R) (l : Rbar) : is_lim_seq u l -> l <> 0 -> is_lim_seq (fun n => / u n) (Rbar_inv l).
Proof.
intros Hu Hl.
apply filterlim_comp with (1 := Hu).
Admitted.

Lemma ex_lim_seq_inv (u : nat -> R) : ex_lim_seq u -> Lim_seq u <> 0 -> ex_lim_seq (fun n => / u n).
Proof.
intros.
apply Lim_seq_correct in H.
exists (Rbar_inv (Lim_seq u)).
Admitted.

Lemma Lim_seq_inv (u : nat -> R) : ex_lim_seq u -> (Lim_seq u <> 0) -> Lim_seq (fun n => / u n) = Rbar_inv (Lim_seq u).
Proof.
move => Hl Hu.
apply is_lim_seq_unique.
apply is_lim_seq_inv.
by apply Lim_seq_correct.
Admitted.

Lemma filterlim_Rbar_mult : forall x y z, is_Rbar_mult x y z -> filterlim (fun z => fst z * snd z) (filter_prod (Rbar_locally x) (Rbar_locally y)) (Rbar_locally z).
Proof.
intros x y z.
wlog: x y z / (Rbar_le 0 x).
intros Hw.
case: (Rbar_le_lt_dec 0 x) => Hx Hp.
by apply Hw.
apply (filterlim_ext (fun z => - (- fst z * snd z))).
intros t.
ring.
rewrite -(Rbar_opp_involutive z).
eapply filterlim_comp.
2: apply filterlim_Rbar_opp.
assert (Hw' : filterlim (fun z => fst z * snd z) (filter_prod (Rbar_locally (Rbar_opp x)) (Rbar_locally y)) (Rbar_locally (Rbar_opp z))).
apply Hw.
replace (Finite 0) with (Rbar_opp 0) by apply (f_equal Finite), Ropp_0.
apply Rbar_opp_le.
by apply Rbar_lt_le.
by apply is_Rbar_mult_opp_l.
clear Hw.
intros P HP.
specialize (Hw' P HP).
destruct Hw' as [Q R H1 H2 H3].
exists (fun x => Q (- x)) R.
now apply filterlim_Rbar_opp.
exact H2.
intros u v HQ HR.
exact (H3 _ _ HQ HR).
wlog: x y z / (Rbar_le 0 y).
intros Hw.
case: (Rbar_le_lt_dec 0 y) => Hy Hx Hp.
by apply Hw.
apply (filterlim_ext (fun z => - (fst z * -snd z))).
intros t.
ring.
rewrite -(Rbar_opp_involutive z).
eapply filterlim_comp.
2: apply filterlim_Rbar_opp.
assert (Hw' : filterlim (fun z => fst z * snd z) (filter_prod (Rbar_locally x) (Rbar_locally (Rbar_opp y))) (Rbar_locally (Rbar_opp z))).
apply Hw.
replace (Finite 0) with (Rbar_opp 0) by apply (f_equal Finite), Ropp_0.
apply Rbar_opp_le.
by apply Rbar_lt_le.
by [].
by apply is_Rbar_mult_opp_r.
clear Hw.
intros P HP.
specialize (Hw' P HP).
destruct Hw' as [Q R H1 H2 H3].
exists Q (fun x => R (- x)).
exact H1.
now apply filterlim_Rbar_opp.
intros u v HQ HR.
exact (H3 _ _ HQ HR).
wlog: x y z / (Rbar_le x y).
intros Hw.
case: (Rbar_le_lt_dec x y) => Hl Hx Hy Hp.
by apply Hw.
assert (Hw' : filterlim (fun z => fst z * snd z) (filter_prod (Rbar_locally y) (Rbar_locally x)) (Rbar_locally z)).
apply Hw ; try assumption.
by apply Rbar_lt_le.
by apply is_Rbar_mult_sym.
intros P HP.
specialize (Hw' P HP).
destruct Hw' as [Q R H1 H2 H3].
exists R Q ; try assumption.
intros u v HR HQ.
simpl.
rewrite Rmult_comm.
exact (H3 _ _ HQ HR).
case: x => [x| | ] ; case: y => [y| | ] ; case: z => [z| | ] Hl Hy Hx Hp ; try (by case: Hl) || (by case: Hx) || (by case: Hy).
case: Hp => <-.
intros P [eps HP].
assert (He: 0 < eps / (x + y + 1)).
apply Rdiv_lt_0_compat.
apply cond_pos.
apply Rplus_le_lt_0_compat.
now apply Rplus_le_le_0_compat.
apply Rlt_0_1.
set (d := mkposreal _ (Rmin_stable_in_posreal (mkposreal _ Rlt_0_1) (mkposreal _ He))).
exists (fun u => Rabs (u - x) < d) (fun v => Rabs (v - y) < d).
now exists d.
now exists d.
simpl.
intros u v Hu Hv.
apply HP.
rewrite /ball /= /AbsRing_ball /abs /minus /plus /opp /=.
replace (u * v + - (x * y)) with (x * (v - y) + y * (u - x) + (u - x) * (v - y)) by ring.
replace (pos eps) with (x * (eps / (x + y + 1)) + y * (eps / (x + y + 1)) + 1 * (eps / (x + y + 1))).
apply Rle_lt_trans with (1 := Rabs_triang _ _).
apply Rplus_le_lt_compat.
apply Rle_trans with (1 := Rabs_triang _ _).
apply Rplus_le_compat.
rewrite Rabs_mult Rabs_pos_eq //.
apply Rmult_le_compat_l with (1 := Hx).
apply Rlt_le.
apply Rlt_le_trans with (1 := Hv).
apply Rmin_r.
rewrite Rabs_mult Rabs_pos_eq //.
apply Rmult_le_compat_l with (1 := Hy).
apply Rlt_le.
apply Rlt_le_trans with (1 := Hu).
apply Rmin_r.
rewrite Rabs_mult.
apply Rmult_le_0_lt_compat ; try apply Rabs_pos.
apply Rlt_le_trans with (1 := Hu).
apply Rmin_l.
apply Rlt_le_trans with (1 := Hv).
apply Rmin_r.
field.
apply Rgt_not_eq.
apply Rplus_le_lt_0_compat.
now apply Rplus_le_le_0_compat.
apply Rlt_0_1.
move: Hp ; unfold is_Rbar_mult, Rbar_mult'.
case: Rle_dec => // Hx'.
case: Rle_lt_or_eq_dec => {Hl Hx Hy Hx'} // Hx.
move: Hp ; unfold is_Rbar_mult, Rbar_mult'.
case: Rle_dec => // Hx'.
case: Rle_lt_or_eq_dec => {Hl Hx Hy Hx'} // Hx _.
intros P [N HN].
exists (fun u => Rabs (u - x) < x / 2) (fun v => Rmax 0 (N / (x / 2)) < v).
now exists (pos_div_2 (mkposreal _ Hx)).
now exists (Rmax 0 (N / (x / 2))).
intros u v Hu Hv.
simpl.
apply HN.
apply Rle_lt_trans with ((x - x / 2) * Rmax 0 (N / (x / 2))).
apply Rmax_case_strong => H.
rewrite Rmult_0_r ; apply Rnot_lt_le ; contradict H ; apply Rlt_not_le.
repeat apply Rdiv_lt_0_compat => //.
by apply Rlt_R0_R2.
apply Req_le ; field.
by apply Rgt_not_eq.
apply Rmult_le_0_lt_compat.
lra.
apply Rmax_l.
now apply Rabs_lt_between'.
exact Hv.
move: Hp ; unfold is_Rbar_mult, Rbar_mult'.
case: Rle_dec => // Hx'.
case: Rle_lt_or_eq_dec => {Hl Hx Hy Hx'} // Hx.
clear.
intros P [N HN].
exists (fun u => 1 < u) (fun v => Rabs N < v).
now exists 1.
now exists (Rabs N).
intros u v Hu Hv.
simpl.
apply HN.
apply Rle_lt_trans with (1 := Rle_abs _).
rewrite -(Rmult_1_l (Rabs N)).
apply Rmult_le_0_lt_compat.
by apply Rle_0_1.
by apply Rabs_pos.
exact Hu.
Admitted.

Lemma is_lim_seq_mult (u v : nat -> R) (l1 l2 l : Rbar) : is_lim_seq u l1 -> is_lim_seq v l2 -> is_Rbar_mult l1 l2 l -> is_lim_seq (fun n => u n * v n) l.
Proof.
intros Hu Hv Hp.
eapply filterlim_comp_2 ; try eassumption.
Admitted.

Lemma is_lim_seq_mult' (u v : nat -> R) (l1 l2 : R) : is_lim_seq u l1 -> is_lim_seq v l2 -> is_lim_seq (fun n => u n * v n) (l1 * l2).
Proof.
intros Hu Hv.
eapply is_lim_seq_mult ; try eassumption.
Admitted.

Lemma Lim_seq_mult (u v : nat -> R) : ex_lim_seq u -> ex_lim_seq v -> ex_Rbar_mult (Lim_seq u) (Lim_seq v) -> Lim_seq (fun n => u n * v n) = Rbar_mult (Lim_seq u) (Lim_seq v).
Proof.
move => H1 H2 Hl.
apply is_lim_seq_unique.
eapply is_lim_seq_mult ; try apply Lim_seq_correct ; try eassumption.
Admitted.

Lemma filterlim_Rbar_mult_l : forall (a : R) (l : Rbar), filterlim (Rmult a) (Rbar_locally l) (Rbar_locally (Rbar_mult a l)).
Proof.
intros a l.
case: (Req_dec a 0) => [->|Ha].
apply (filterlim_ext (fun _ => 0)).
intros x.
apply sym_eq, Rmult_0_l.
rewrite Rbar_mult_0_l.
apply filterlim_const.
eapply filterlim_comp_2.
apply filterlim_const.
apply filterlim_id.
eapply (filterlim_Rbar_mult a l).
Admitted.

Lemma filterlim_Rbar_mult_r : forall (a : R) (l : Rbar), filterlim (fun x => Rmult x a) (Rbar_locally l) (Rbar_locally (Rbar_mult l a)).
Proof.
intros a l.
apply (filterlim_ext (fun x => a * x)).
apply Rmult_comm.
rewrite Rbar_mult_comm.
Admitted.

Lemma is_lim_seq_scal_l (u : nat -> R) (a : R) (lu : Rbar) : is_lim_seq u lu -> is_lim_seq (fun n => a * u n) (Rbar_mult a lu).
Proof.
intros Hu H.
apply filterlim_comp with (1 := Hu).
Admitted.

Lemma ex_lim_seq_scal_l (u : nat -> R) (a : R) : ex_lim_seq u -> ex_lim_seq (fun n => a * u n).
Proof.
move => [l H].
exists (Rbar_mult a l).
Admitted.

Lemma Lim_seq_scal_l (u : nat -> R) (a : R) : Lim_seq (fun n => a * u n) = Rbar_mult a (Lim_seq u).
Proof.
case: (Req_dec a 0) => [ -> | Ha].
rewrite -(Lim_seq_ext (fun _ => 0)) /=.
rewrite Lim_seq_const.
case: (Lim_seq u) => [x | | ] //=.
by rewrite Rmult_0_l.
case: Rle_dec (Rle_refl 0) => // H _.
case: Rle_lt_or_eq_dec (Rlt_irrefl 0) => // _ _.
case: Rle_dec (Rle_refl 0) => // H _.
case: Rle_lt_or_eq_dec (Rlt_irrefl 0) => // _ _.
move => n ; by rewrite Rmult_0_l.
wlog: a u Ha / (0 < a) => [Hw | {Ha} Ha].
case: (Rlt_le_dec 0 a) => Ha'.
by apply Hw.
case: Ha' => // Ha'.
rewrite -(Lim_seq_ext (fun n => - a * - u n)).
rewrite -Rbar_mult_opp.
rewrite -Lim_seq_opp.
apply Hw.
contradict Ha ; rewrite -(Ropp_involutive a) Ha ; ring.
apply Ropp_lt_cancel ; by rewrite Ropp_0 Ropp_involutive.
move => n ; ring.
rewrite /Lim_seq.
rewrite {2}/LimSup_seq ; case: ex_LimSup_seq => ls Hs ; rewrite {2}/LimInf_seq ; case: ex_LimInf_seq => li Hi ; simpl proj1_sig.
apply (is_LimSup_seq_scal_pos a) in Hs => //.
apply (is_LimInf_seq_scal_pos a) in Hi => //.
rewrite (is_LimSup_seq_unique _ _ Hs).
rewrite (is_LimInf_seq_unique _ _ Hi).
Admitted.

Lemma is_lim_seq_scal_r (u : nat -> R) (a : R) (lu : Rbar) : is_lim_seq u lu -> is_lim_seq (fun n => u n * a) (Rbar_mult lu a).
Proof.
move => Hu Ha.
apply is_lim_seq_ext with ((fun n : nat => a * u n)).
move => n ; by apply Rmult_comm.
rewrite Rbar_mult_comm.
apply is_lim_seq_scal_l.
Admitted.

Lemma ex_lim_seq_scal_r (u : nat -> R) (a : R) : ex_lim_seq u -> ex_lim_seq (fun n => u n * a).
Proof.
move => Hu.
apply ex_lim_seq_ext with ((fun n : nat => a * u n)) ; try by intuition.
apply ex_lim_seq_scal_l.
Admitted.

Lemma Lim_seq_scal_r (u : nat -> R) (a : R) : Lim_seq (fun n => u n * a) = Rbar_mult (Lim_seq u) a.
Proof.
rewrite Rbar_mult_comm -Lim_seq_scal_l.
Admitted.

Lemma is_lim_seq_div (u v : nat -> R) (l1 l2 l : Rbar) : is_lim_seq u l1 -> is_lim_seq v l2 -> l2 <> 0 -> is_Rbar_div l1 l2 l -> is_lim_seq (fun n => u n / v n) l.
Proof.
intros.
eapply is_lim_seq_mult ; try eassumption.
Admitted.

Lemma is_lim_seq_div' (u v : nat -> R) (l1 l2 : R) : is_lim_seq u l1 -> is_lim_seq v l2 -> l2 <> 0 -> is_lim_seq (fun n => u n / v n) (l1 / l2).
Proof.
intros.
eapply is_lim_seq_div ; try eassumption.
now contradict H1 ; case: H1 => ->.
Admitted.

Lemma ex_lim_seq_div (u v : nat -> R) : ex_lim_seq u -> ex_lim_seq v -> Lim_seq v <> 0 -> ex_Rbar_div (Lim_seq u) (Lim_seq v) -> ex_lim_seq (fun n => u n / v n).
Proof.
intros.
apply Lim_seq_correct in H.
apply Lim_seq_correct in H0.
exists (Rbar_div (Lim_seq u) (Lim_seq v)).
eapply is_lim_seq_div ; try eassumption.
Admitted.

Lemma Lim_seq_div (u v : nat -> R) : ex_lim_seq u -> ex_lim_seq v -> (Lim_seq v <> 0) -> ex_Rbar_div (Lim_seq u) (Lim_seq v) -> Lim_seq (fun n => u n / v n) = Rbar_div (Lim_seq u) (Lim_seq v).
Proof.
move => H0 H1 H2 H3.
apply is_lim_seq_unique.
eapply is_lim_seq_div ; try apply Lim_seq_correct ; try eassumption.
Admitted.

Lemma ex_lim_seq_adj (u v : nat -> R) : (forall n, u n <= u (S n)) -> (forall n, v (S n) <= v n) -> is_lim_seq (fun n => v n - u n) 0 -> ex_finite_lim_seq u /\ ex_finite_lim_seq v /\ Lim_seq u = Lim_seq v.
Proof.
move => Hu Hv H0.
suff H : forall n, u n <= v n.
suff Eu : ex_finite_lim_seq u.
split ; try auto.
suff Ev : ex_finite_lim_seq v.
split ; try auto.
apply is_lim_seq_unique in H0.
rewrite Lim_seq_minus in H0 ; try by intuition.
apply ex_finite_lim_seq_correct in Eu.
apply ex_finite_lim_seq_correct in Ev.
rewrite -(proj2 Eu) -(proj2 Ev) /= in H0 |- *.
apply Rbar_finite_eq in H0 ; apply Rbar_finite_eq.
by apply sym_eq, Rminus_diag_uniq, H0.
by apply ex_finite_lim_seq_correct.
by apply ex_finite_lim_seq_correct.
apply ex_finite_lim_seq_correct in Eu.
apply ex_finite_lim_seq_correct in Ev.
by rewrite -(proj2 Eu) -(proj2 Ev).
apply ex_finite_lim_seq_decr with (u O) => //.
move => n ; apply Rle_trans with (2 := H _).
elim: n => [ | n IH].
by apply Rle_refl.
by apply Rle_trans with (2 := Hu _).
apply ex_finite_lim_seq_incr with (v O) => //.
move => n ; apply Rle_trans with (1 := H _).
elim: n => [ | n IH].
by apply Rle_refl.
by apply Rle_trans with (1 := Hv _).
move => n0 ; apply Rnot_lt_le ; move/Rminus_lt_0 => H.
apply is_lim_seq_spec in H0.
case: (H0 (mkposreal _ H)) => /= {H0} N H0.
move: (H0 _ (le_plus_r n0 N)) ; apply Rle_not_lt.
rewrite Rminus_0_r ; apply Rle_trans with (2 := Rabs_maj2 _).
rewrite Ropp_minus_distr'.
apply Rplus_le_compat, Ropp_le_contravar.
elim: (N) => [ | m IH].
rewrite plus_0_r ; apply Rle_refl.
rewrite -plus_n_Sm ; by apply Rle_trans with (2 := Hu _).
elim: (N) => [ | m IH].
rewrite plus_0_r ; apply Rle_refl.
Admitted.

Lemma is_lim_seq_continuous (f : R -> R) (u : nat -> R) (l : R) : continuity_pt f l -> is_lim_seq u l -> is_lim_seq (fun n => f (u n)) (f l).
Proof.
move => Cf Hu.
apply continuity_pt_filterlim in Cf.
apply filterlim_comp with (1 := Hu).
Admitted.

Lemma filterlim_Rabs : forall l : Rbar, filterlim Rabs (Rbar_locally l) (Rbar_locally (Rbar_abs l)).
Proof.
case => [l| |] /=.
apply @filterlim_norm.
intros P [N HP].
exists N => x Hx.
apply HP.
apply Rlt_le_trans with (1 := Hx).
apply Rle_abs.
intros P [N HP].
exists (-N) => x Hx.
apply HP.
apply Rlt_le_trans with (2 := Rabs_maj2 _), Ropp_lt_cancel.
Admitted.

Lemma is_lim_seq_abs (u : nat -> R) (l : Rbar) : is_lim_seq u l -> is_lim_seq (fun n => Rabs (u n)) (Rbar_abs l).
Proof.
intros Hu.
apply filterlim_comp with (1 := Hu).
Admitted.

Lemma ex_lim_seq_abs (u : nat -> R) : ex_lim_seq u -> ex_lim_seq (fun n => Rabs (u n)).
Proof.
move => [l Hu].
Admitted.

Lemma Lim_seq_abs (u : nat -> R) : ex_lim_seq u -> Lim_seq (fun n => Rabs (u n)) = Rbar_abs (Lim_seq u).
Proof.
intros.
apply is_lim_seq_unique.
apply is_lim_seq_abs.
Admitted.

Lemma is_lim_seq_abs_0 (u : nat -> R) : is_lim_seq u 0 <-> is_lim_seq (fun n => Rabs (u n)) 0.
Proof.
split => Hu.
rewrite -Rabs_R0.
by apply (is_lim_seq_abs _ 0).
apply is_lim_seq_spec in Hu.
apply is_lim_seq_spec.
move => eps.
case: (Hu eps) => {Hu} N Hu.
exists N => n Hn.
Admitted.

Lemma ex_lim_seq_mult (u v : nat -> R) : ex_lim_seq u -> ex_lim_seq v -> ex_Rbar_mult (Lim_seq u) (Lim_seq v) -> ex_lim_seq (fun n => u n * v n).
Proof.
intros [lu Hu] [lv Hv] H ; exists (Rbar_mult lu lv).
eapply is_lim_seq_mult ; try eassumption.
rewrite -(is_lim_seq_unique u lu) //.
rewrite -(is_lim_seq_unique v lv) //.
by apply Rbar_mult_correct.
