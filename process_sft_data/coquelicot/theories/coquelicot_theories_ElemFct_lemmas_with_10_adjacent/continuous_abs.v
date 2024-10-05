Require Import Reals Omega mathcomp.ssreflect.ssreflect.
Require Import Rbar Rcomplements Continuity Derive Hierarchy RInt PSeries.
Require Import Lim_seq RInt_analysis.
Section nat_to_ring.
Context {K : Ring}.
Definition nat_to_ring (n : nat) : K := sum_n_m (fun _ => one) 1 n.
End nat_to_ring.
Section is_derive_mult.
Context {K : AbsRing}.
End is_derive_mult.

Lemma filterlim_abs_0 {K : AbsRing} : (forall x : K, abs x = 0 -> x = zero) -> filterlim (abs (K := K)) (locally' (zero (G := K))) (at_right 0).
Proof.
intros H P [eps HP].
exists eps.
intros x Hx Hx'.
apply HP.
revert Hx.
rewrite /ball /= /AbsRing_ball !minus_zero_r {2}/abs /= Rabs_pos_eq.
by [].
by apply abs_ge_0.
assert (abs x <> 0).
contradict Hx' ; by apply H.
case: (abs_ge_0 x) => // H1.
Admitted.

Lemma continuous_Rabs (x : R) : continuous Rabs x.
Proof.
Admitted.

Lemma filterlim_Rabs (x : Rbar) : filterlim Rabs (Rbar_locally' x) (Rbar_locally (Rbar_abs x)).
Proof.
destruct x as [x| | ] => //=.
eapply filterlim_filter_le_1, continuous_Rabs.
intros P [d HP] ; exists d => y Hy _.
by apply HP.
eapply filterlim_ext_loc.
exists 0 => y Hy.
rewrite Rabs_pos_eq // ; by apply Rlt_le.
apply is_lim_id.
eapply filterlim_ext_loc.
exists 0 => y Hy.
rewrite -Rabs_Ropp Rabs_pos_eq // -Ropp_0 ; by apply Ropp_le_contravar, Rlt_le.
Admitted.

Lemma is_lim_Rabs (f : R -> R) (x l : Rbar) : is_lim f x l -> is_lim (fun x => Rabs (f x)) x (Rbar_abs l).
Proof.
destruct l as [l| | ] ; simpl ; intros ; first last.
eapply is_lim_comp.
2: by apply H.
by apply filterlim_Rabs.
destruct x ; by exists (mkposreal _ Rlt_0_1).
eapply is_lim_comp.
2: by apply H.
by apply filterlim_Rabs.
destruct x ; by exists (mkposreal _ Rlt_0_1).
apply is_lim_comp_continuous => //.
Admitted.

Lemma filterlim_Rabs_0 : filterlim Rabs (Rbar_locally' 0) (at_right 0).
Proof.
apply @filterlim_abs_0.
Admitted.

Lemma is_lim_Rabs_0 (f : R -> R) (x : Rbar) : is_lim f x 0 -> Rbar_locally' x (fun x => f x <> 0) -> filterlim (fun x => Rabs (f x)) (Rbar_locally' x) (at_right 0).
Proof.
intros.
eapply filterlim_comp, filterlim_Rabs_0.
intros P HP.
apply H in HP.
generalize (filter_and _ _ H0 HP).
rewrite /filtermap /= ; apply filter_imp.
intros y Hy.
Admitted.

Lemma filterdiff_Rabs (x : R) : x <> 0 -> filterdiff Rabs (locally x) (fun y : R => scal y (sign x)).
Proof.
rewrite -/(is_derive Rabs x (sign x)).
move => Hx0.
case: (Rle_lt_dec 0 x) => Hx.
case: Hx => //= Hx.
rewrite sign_eq_1 //.
eapply is_derive_ext_loc.
apply locally_interval with 0 p_infty.
by [].
by [].
move => /= y Hy _.
rewrite Rabs_pos_eq //.
by apply Rlt_le.
by apply @is_derive_id.
by apply sym_eq in Hx.
rewrite sign_eq_m1 //.
eapply is_derive_ext_loc.
apply locally_interval with m_infty 0.
by [].
by [].
move => /= y _ Hy.
rewrite -Rabs_Ropp Rabs_pos_eq //.
rewrite -Ropp_0 ; by apply Rlt_le, Ropp_lt_contravar.
apply @is_derive_opp.
Admitted.

Lemma is_derive_Rabs (f : R -> R) (x df : R) : is_derive f x df -> f x <> 0 -> is_derive (fun x => Rabs (f x)) x (sign (f x) * df).
Proof.
intros Hf Hfx.
evar_last.
apply is_derive_comp, Hf.
by apply filterdiff_Rabs.
Admitted.

Lemma filterlim_Rinv_0_right : filterlim Rinv (at_right 0) (Rbar_locally p_infty).
Proof.
intros P [M HM].
have Hd : 0 < / Rmax 1 M.
apply Rinv_0_lt_compat.
apply Rlt_le_trans with (2 := Rmax_l _ _).
by apply Rlt_0_1.
exists (mkposreal _ Hd) => x /= Hx Hx0.
apply HM.
apply Rle_lt_trans with (1 := Rmax_r 1 M).
replace (Rmax 1 M) with (/ / Rmax 1 M) by (field ; apply Rgt_not_eq, Rlt_le_trans with (2 := Rmax_l _ _), Rlt_0_1).
apply Rinv_lt_contravar.
apply Rdiv_lt_0_compat with (1 := Hx0).
apply Rlt_le_trans with (2 := Rmax_l _ _), Rlt_0_1.
rewrite /ball /= /AbsRing_ball /= /abs /minus /plus /opp /= in Hx.
rewrite -/(Rminus _ _) Rminus_0_r Rabs_pos_eq // in Hx.
Admitted.

Lemma is_lim_Rinv_0_right (f : R -> R) (x : Rbar) : is_lim f x 0 -> Rbar_locally' x (fun x => 0 < f x) -> is_lim (fun x => / (f x)) x p_infty.
Proof.
intros.
eapply filterlim_comp, filterlim_Rinv_0_right.
intros P HP.
apply H in HP.
generalize (filter_and _ _ H0 HP).
rewrite /filtermap ; apply filter_imp => y Hy.
Admitted.

Lemma continuous_abs {K : AbsRing} (x : K) : continuous abs x.
Proof.
apply filterlim_locally => /= eps.
exists eps => /= y Hy.
eapply Rle_lt_trans, Hy.
wlog: x y Hy / (abs x <= abs y) => [Hw | Hxy].
case: (Rle_lt_dec (abs x) (abs y)) => Hxy.
by apply Hw.
rewrite abs_minus (abs_minus y).
apply Hw, Rlt_le, Hxy.
by apply ball_sym.
rewrite {1}/abs /=.
rewrite Rabs_pos_eq.
apply Rle_minus_l.
eapply Rle_trans, abs_triangle.
apply Req_le, f_equal.
by rewrite /minus -plus_assoc plus_opp_l plus_zero_r.
by apply -> Rminus_le_0.
