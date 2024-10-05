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

Lemma is_lim_seq_geom (q : R) : Rabs q < 1 -> is_lim_seq (fun n => q ^ n) 0.
Proof.
intros Hq.
apply is_lim_seq_spec.
move => [e He] /=.
case: (pow_lt_1_zero q Hq e He) => N H.
exists N => n Hn.
Admitted.

Lemma ex_lim_seq_geom (q : R) : Rabs q < 1 -> ex_lim_seq (fun n => q ^ n).
Proof.
Admitted.

Lemma Lim_seq_geom (q : R) : Rabs q < 1 -> Lim_seq (fun n => q ^ n) = 0.
Proof.
intros.
apply is_lim_seq_unique.
Admitted.

Lemma Lim_seq_div (u v : nat -> R) : ex_lim_seq u -> ex_lim_seq v -> (Lim_seq v <> 0) -> ex_Rbar_div (Lim_seq u) (Lim_seq v) -> Lim_seq (fun n => u n / v n) = Rbar_div (Lim_seq u) (Lim_seq v).
Proof.
move => H0 H1 H2 H3.
apply is_lim_seq_unique.
eapply is_lim_seq_div ; try apply Lim_seq_correct ; try eassumption.
by apply Rbar_mult_correct.
