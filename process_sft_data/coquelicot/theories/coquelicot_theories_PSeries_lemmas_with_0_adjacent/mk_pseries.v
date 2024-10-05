Require Import Reals Even Div2 Omega Psatz.
Require Import mathcomp.ssreflect.ssreflect.
Require Import Rcomplements Rbar Lim_seq Lub Hierarchy.
Require Import Continuity Derive Seq_fct Series.
Section Definitions.
Context {K : AbsRing} {V : NormedModule K}.
Definition is_pseries (a : nat -> V) (x:K) (l : V) := is_series (fun k => scal (pow_n x k) (a k)) l.
Definition ex_pseries (a : nat -> V) (x : K) := ex_series (fun k => scal (pow_n x k) (a k)).
End Definitions.
Definition PSeries (a : nat -> R) (x : R) : R := Series (fun k => a k * x ^ k).
Section Extensionality.
Context {K : AbsRing} {V : NormedModule K}.
End Extensionality.
Section ConvergenceCircle.
Context {K : AbsRing} {V : NormedModule K}.
End ConvergenceCircle.
Definition CV_disk (a : nat -> R) (r : R) := ex_series (fun n => Rabs (a n * r^n)).
Definition CV_radius (a : nat -> R) : Rbar := Lub_Rbar (CV_disk a).
Section PS_plus.
Context {K : AbsRing} {V : NormedModule K}.
Definition PS_plus (a b : nat -> V) (n : nat) : V := plus (a n) (b n).
End PS_plus.
Section PS_scal.
Context {K : AbsRing} {V : NormedModule K}.
Definition PS_scal (c : K) (a : nat -> V) (n : nat) : V := scal c (a n).
End PS_scal.
Definition PS_scal_r (c : R) (a : nat -> R) (n : nat) : R := a n * c.
Section PS_incr.
Context {K : AbsRing} {V : NormedModule K}.
Definition PS_incr_1 (a : nat -> V) (n : nat) : V := match n with | 0 => zero | S n => a n end.
Fixpoint PS_incr_n (a : nat -> V) (n k : nat) : V := match n with | O => a k | S n => PS_incr_1 (PS_incr_n a n) k end.
Definition PS_decr_1 (a : nat -> V) (n : nat) : V := a (S n).
Definition PS_decr_n (a : nat -> V) (n k : nat) : V := a (n + k)%nat.
End PS_incr.
Definition PS_mult (a b : nat -> R) n := sum_f_R0 (fun k => a k * b (n - k)%nat) n.
Section PS_opp.
Context {K : AbsRing} {V : NormedModule K}.
Definition PS_opp (a : nat -> V) (n : nat) : V := opp (a n).
End PS_opp.
Section PS_minus.
Context {K : AbsRing} {V : NormedModule K}.
Definition PS_minus (a b : nat -> V) (n : nat) : V := plus (a n) (opp (b n)).
End PS_minus.
Definition PS_derive (a : nat -> R) (n : nat) := INR (S n) * a (S n).
Definition PS_derive_n (n : nat) (a : nat -> R) := (fun k => (INR (fact (k + n)%nat) / INR (fact k)) * a (k + n)%nat).

Lemma mk_pseries (f : R -> R) (M : R) (r : Rbar) : (forall n x, Rbar_lt (Finite (Rabs x)) r -> (ex_derive_n f n x) /\ Rabs (Derive_n f n x) <= M) -> forall x, Rbar_lt (Finite (Rabs x)) r -> is_pseries (fun n => Derive_n f n 0 / INR (fact n)) x (f x).
Proof.
move => Hd x Hx.
wlog: r Hx Hd /(Finite (real r) = r) => [Hw | Hr].
case: r Hx Hd => /= [r | | ] Hx Hd.
by apply (Hw (Finite r)).
apply (Hw (Finite (Rabs x+1))).
simpl ; exact: Rlt_plus_1.
move => n y Hy ; by apply Hd.
by [].
by [].
rewrite -Hr in Hx Hd.
move: (real r) Hx Hd => /= {r Hr} r Hx Hd.
wlog: x Hx f Hd / (0 < x) => [Hw | Hx'].
case: (total_order_T 0 x) => Hx'.
case: Hx' => Hx'.
by apply Hw.
rewrite -Hx'.
replace (f 0) with (Derive_n f O 0 / INR (fact O)) by (simpl ; field).
apply @is_pseries_0.
rewrite -Rabs_Ropp in Hx.
suff Hf : (forall (n : nat) (x : R), ((Rabs x)) < r -> ex_derive_n (fun x0 : R => f (- x0)) n x /\ Rabs (Derive_n (fun x0 : R => f (- x0)) n x) <= M).
move: (Hw _ Hx (fun x => f (-x)) Hf (Ropp_0_gt_lt_contravar _ Hx')) => {Hw} Hw.
rewrite Ropp_involutive in Hw.
apply is_series_ext with (2:=Hw).
intros n; rewrite Derive_n_comp_opp; simpl.
rewrite /scal /= /mult /=.
apply trans_eq with ((pow_n (K := R_AbsRing) (- x) n * (-1) ^ n) * (Derive_n f n (- 0) / INR (fact n)));[unfold Rdiv; ring|idtac].
rewrite Ropp_0.
apply f_equal2; try reflexivity.
clear; induction n; simpl.
apply Rmult_1_l.
rewrite /mult /=.
rewrite <- IHn; ring.
rewrite Ropp_0 ; exists (mkposreal r (Rle_lt_trans _ _ _ (Rabs_pos _) Hx)) => /= y Hy k Hk.
rewrite /ball /= /AbsRing_ball /= /minus /plus /opp /= -/(Rminus _ _) Rminus_0_r in Hy.
by apply (Hd k).
move => {x Hx Hx'} n x Hx.
rewrite Derive_n_comp_opp.
split.
apply ex_derive_n_comp_opp.
apply Rabs_lt_between in Hx.
case: Hx => Hx1 Hx2.
apply Rminus_lt_0 in Hx1.
apply Rminus_lt_0 in Hx2.
have Hx := Rmin_pos _ _ Hx1 Hx2 => {Hx1 Hx2}.
exists (mkposreal _ Hx) => /= y Hy k Hk.
rewrite /ball /= /AbsRing_ball /= in Hy.
apply Rabs_lt_between' in Hy.
rewrite /Rminus -Rmax_opp_Rmin Rplus_max_distr_l Rplus_min_distr_l in Hy.
case: Hy => Hy1 Hy2.
apply Rle_lt_trans with (1 := Rmax_r _ _) in Hy1.
ring_simplify in Hy1.
apply Rlt_le_trans with (2 := Rmin_l _ _) in Hy2.
ring_simplify in Hy2.
apply (Hd k y).
apply Rabs_lt_between.
by split.
rewrite Rabs_mult -RPow_abs Rabs_Ropp Rabs_R1 pow1 Rmult_1_l.
apply Hd.
by rewrite Rabs_Ropp.
apply Rabs_lt_between in Hx.
case: Hx => Hx1 Hx2.
apply Rminus_lt_0 in Hx1.
apply Rminus_lt_0 in Hx2.
have Hx := Rmin_pos _ _ Hx1 Hx2 => {Hx1 Hx2}.
exists (mkposreal _ Hx) => /= y Hy k Hk.
rewrite /ball /= /AbsRing_ball /= in Hy.
apply Rabs_lt_between' in Hy.
rewrite /Rminus -Rmax_opp_Rmin Rplus_max_distr_l Rplus_min_distr_l in Hy.
case: Hy => Hy1 Hy2.
apply Rle_lt_trans with (1 := Rmax_r _ _) in Hy1.
ring_simplify in Hy1.
apply Rlt_le_trans with (2 := Rmin_l _ _) in Hy2.
ring_simplify in Hy2.
apply (Hd k y).
apply Rabs_lt_between.
by split.
move => P [eps Heps].
have : exists N, forall n, (N <= n)%nat -> r ^ (S n) * M / INR (fact (S n)) < eps.
have H : is_lim_seq (fun n => r ^ n * M / INR (fact n)) 0.
case: (Rlt_dec 0 M) => H.
have H0 : forall n : nat, 0 < r ^ n * M / INR (fact n).
move => n.
apply Rdiv_lt_0_compat.
apply Rmult_lt_0_compat.
apply pow_lt.
apply Rle_lt_trans with (2 := Hx), Rabs_pos.
exact: H.
exact: INR_fact_lt_0.
apply ex_series_lim_0, ex_series_Rabs, ex_series_DAlembert with 0.
exact: Rlt_0_1.
move => n ; apply Rgt_not_eq, Rlt_gt, H0.
apply is_lim_seq_ext with (fun n => r / INR (S n)).
move => n ; rewrite Rabs_pos_eq.
rewrite /fact -/fact /pow -/pow ?mult_INR ; field.
repeat split ; apply Rgt_not_eq, Rlt_gt.
exact: INR_fact_lt_0.
by apply (lt_INR O), lt_O_Sn.
exact: H.
apply pow_lt, Rle_lt_trans with (Rabs x), Hx ; by apply Rabs_pos.
apply Rlt_le, Rdiv_lt_0_compat ; by apply H0.
rewrite -(Rmult_0_r r) ; apply (is_lim_seq_scal_l _ _ 0) => //.
apply (is_lim_seq_incr_1 (fun n => / INR n)).
replace (Finite 0) with (Rbar_inv p_infty) by auto.
apply is_lim_seq_inv.
by apply is_lim_seq_INR.
by [].
apply Rnot_lt_le in H ; case: H => H.
contradict H.
apply Rle_not_lt.
apply Rle_trans with (Rabs (Derive_n f O x)).
by apply Rabs_pos.
by apply Hd.
rewrite H.
apply is_lim_seq_ext with (fun _ => 0).
move => n ; rewrite /Rdiv ; ring.
exact: is_lim_seq_const.
apply is_lim_seq_incr_1 in H.
apply is_lim_seq_spec in H.
case: (H eps) => {H} N H.
exists N => n Hn.
apply Rle_lt_trans with (2 := H n Hn).
rewrite Rminus_0_r.
exact: Rle_abs.
case => N HN.
exists N => n Hn.
apply Heps.
case: (Taylor_Lagrange f n 0 x).
by apply Hx'.
move => t Ht k Hk.
apply Hd.
rewrite Rabs_right.
apply Rle_lt_trans with (1 := proj2 Ht).
by apply Rle_lt_trans with (1 := Rle_abs _), Hx.
by apply Rle_ge, Ht.
move => y [Hy ->].
rewrite Rminus_0_r.
rewrite (sum_n_ext _ (fun m : nat => x ^ m / INR (fact m) * Derive_n f m 0)).
rewrite sum_n_Reals.
apply Rle_lt_trans with (2 := HN n Hn).
replace (r ^ S n * M / INR (fact (S n))) with ((r^S n / INR (fact (S n))) * M) by (rewrite /Rdiv ; ring).
change minus with Rminus.
ring_simplify (sum_f_R0 (fun m : nat => x ^ m / INR (fact m) * Derive_n f m 0) n - (sum_f_R0 (fun m : nat => x ^ m / INR (fact m) * Derive_n f m 0) n + x ^ S n / INR (fact (S n)) * Derive_n f (S n) y)).
change abs with Rabs.
rewrite Rabs_mult Rabs_Ropp.
apply Rmult_le_compat.
by apply Rabs_pos.
by apply Rabs_pos.
rewrite Rabs_div.
apply Rmult_le_compat.
apply Rabs_pos.
apply Rlt_le, Rinv_0_lt_compat.
apply Rabs_pos_lt.
exact: INR_fact_neq_0.
rewrite -RPow_abs.
apply pow_incr ; split.
apply Rabs_pos.
by apply Rlt_le.
apply Rle_Rinv.
exact: (INR_fact_lt_0 (S n)).
apply Rabs_pos_lt, INR_fact_neq_0.
apply Rle_abs.
apply INR_fact_neq_0.
apply Hd.
apply Rlt_trans with (2 := Hx).
rewrite ?Rabs_pos_eq.
by apply Hy.
apply Rlt_le, Hx'.
apply Rlt_le, Hy.
intros m; rewrite pow_n_pow.
rewrite /scal /= /mult /= /Rdiv ; ring.
