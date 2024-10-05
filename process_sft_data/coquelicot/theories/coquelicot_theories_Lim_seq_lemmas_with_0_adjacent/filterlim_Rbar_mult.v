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
exact Hv.
