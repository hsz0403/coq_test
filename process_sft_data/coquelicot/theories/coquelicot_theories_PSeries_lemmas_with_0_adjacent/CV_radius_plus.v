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

Lemma CV_radius_plus (a b : nat -> R) : Rbar_le (Rbar_min (CV_radius a) (CV_radius b)) (CV_radius (PS_plus a b)).
Proof.
wlog: a b / (Rbar_le (CV_radius a) (CV_radius b)) => [ Hw | Hle ].
case: (Rbar_le_lt_dec (CV_radius a) (CV_radius b)) => Hle.
by apply Hw.
rewrite Rbar_min_comm.
rewrite (CV_radius_ext (PS_plus a b) (PS_plus b a)).
by apply Hw, Rbar_lt_le.
now intros n ; apply Rplus_comm.
replace (Rbar_min (CV_radius a) (CV_radius b)) with (CV_radius a).
apply is_lub_Rbar_subset with (CV_disk (PS_plus a b)) (fun x => (CV_disk a x) /\ (CV_disk b x)).
move => x [Ha Hb] ; by apply CV_disk_plus.
rewrite /CV_radius /Lub_Rbar ; by case: ex_lub_Rbar.
have Ha : is_lub_Rbar (fun x : R => CV_disk a x) (CV_radius a).
rewrite /CV_radius /Lub_Rbar ; by case: ex_lub_Rbar.
have Hb : is_lub_Rbar (fun x : R => CV_disk b x) (CV_radius b).
rewrite /CV_radius /Lub_Rbar ; by case: ex_lub_Rbar.
split.
intros y [Hay Hby].
by apply Ha.
case: (Rbar_le_lt_or_eq_dec _ _ (CV_radius_ge_0 a)) => Ha0.
intros c Hc.
assert (Rbar_le 0 c).
apply Hc.
split ; by apply CV_disk_0.
case: c Hc H => [c | | ] //= Hc H.
2: by case: (CV_radius a).
apply Rbar_not_lt_le => Hac.
move: (Rbar_lt_le_trans _ _ _ Hac Hle) => Hbc.
eapply Rbar_le_not_lt.
apply (Hc ((c + Rbar_min (c + 1) (CV_radius a)) / 2)).
assert (Rbar_lt (Rabs ((c + Rbar_min (c + 1) (CV_radius a)) / 2)) (CV_radius a)).
case: (CV_radius a) Hac => //= l Hl.
rewrite Rabs_pos_eq.
apply Rlt_div_l.
by apply Rlt_0_2.
replace (l * 2) with (l+l) by ring.
apply Rplus_lt_le_compat => //.
by apply Rmin_r.
apply Rdiv_le_0_compat.
apply Rplus_le_le_0_compat => //.
apply Rmin_case.
apply Rplus_le_le_0_compat => //.
by apply Rle_0_1.
now eapply Rle_trans, Rlt_le, Hl.
by apply Rlt_0_2.
split ; apply CV_disk_inside.
by [].
now eapply Rbar_lt_le_trans, Hle.
case: (CV_radius a) Hac => [l | | ] //= Hl.
apply Rmin_case.
apply Rlt_div_r.
by apply Rlt_0_2.
apply Rminus_lt_0 ; simpl ; ring_simplify.
by apply Rlt_0_1.
apply Rlt_div_r.
by apply Rlt_0_2.
apply Rminus_lt_0 ; simpl ; ring_simplify.
by rewrite Rplus_comm -Rminus_lt_0.
apply Rlt_div_r.
by apply Rlt_0_2.
apply Rminus_lt_0 ; simpl ; ring_simplify.
by apply Rlt_0_1.
rewrite -Ha0 in Ha Hle |- *.
intros c Hc.
apply Hc ; split ; by apply CV_disk_0.
apply Rbar_min_case_strong => //.
by apply Rbar_le_antisym.
