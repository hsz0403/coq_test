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

Lemma is_lim_Rinv_0_left (f : R -> R) (x : Rbar) : is_lim f x 0 -> Rbar_locally' x (fun x => f x < 0) -> is_lim (fun x => / (f x)) x m_infty.
Proof.
intros.
eapply filterlim_comp, filterlim_Rinv_0_left.
intros P HP.
apply H in HP.
generalize (filter_and _ _ H0 HP).
rewrite /filtermap ; apply filter_imp => y Hy.
Admitted.

Lemma filterlim_sqrt_p : filterlim sqrt (Rbar_locally' p_infty) (Rbar_locally p_infty).
Proof.
apply is_lim_spec.
move => M.
exists ((Rmax 0 M)²) => x Hx.
apply Rle_lt_trans with (1 := Rmax_r 0 M).
rewrite -(sqrt_Rsqr (Rmax 0 M)).
apply sqrt_lt_1_alt.
split.
apply Rle_0_sqr.
by apply Hx.
Admitted.

Lemma is_lim_sqrt_p (f : R -> R) (x : Rbar) : is_lim f x p_infty -> is_lim (fun x => sqrt (f x)) x p_infty.
Proof.
intros.
eapply filterlim_comp, filterlim_sqrt_p.
Admitted.

Lemma filterdiff_sqrt (x : R) : 0 < x -> filterdiff sqrt (locally x) (fun y => scal y (/ (2 * sqrt x))).
Proof.
intros Hx.
apply is_derive_Reals.
Admitted.

Lemma is_derive_sqrt (f : R -> R) (x df : R) : is_derive f x df -> 0 < f x -> is_derive (fun x => sqrt (f x)) x (df / (2 * sqrt (f x))).
Proof.
intros Hf Hfx.
evar_last.
eapply is_derive_comp.
by apply filterdiff_sqrt.
by apply Hf.
Admitted.

Lemma nat_to_ring_O : nat_to_ring O = zero.
Proof.
Admitted.

Lemma nat_to_ring_Sn (n : nat) : nat_to_ring (S n) = plus (nat_to_ring n) one.
Proof.
case: n => [ | n] ; rewrite /nat_to_ring.
rewrite sum_n_n sum_n_m_zero //.
by rewrite plus_zero_l.
rewrite sum_n_Sm //.
Admitted.

Lemma is_derive_mult (f g : K -> K) x (df dg : K) : is_derive f x df -> is_derive g x dg -> (forall n m : K, mult n m = mult m n) -> is_derive (fun x : K => mult (f x) (g x)) x (plus (mult df (g x)) (mult (f x) dg)).
Proof.
intros Hf Hg Hmult.
eapply filterdiff_ext_lin.
eapply filterdiff_comp_2 => /=.
by apply Hf.
by apply Hg.
eapply filterdiff_ext_lin.
apply (filterdiff_mult (f x,g x)) => /=.
intros P [d Hd].
assert (Cf := ex_derive_continuous f x).
assert (Cg := ex_derive_continuous g x).
destruct (fun H => proj1 (filterlim_locally _ _) (Cf H) d) as [d1 Hd1].
eexists ; by apply Hf.
destruct (fun H => proj1 (filterlim_locally _ _) (Cg H) d) as [d2 Hd2].
eexists ; by apply Hg.
exists (mkposreal _ (Rmin_stable_in_posreal d1 d2)) => /= y Hy.
apply Hd ; split => /=.
eapply (Hd1 y), ball_le, Hy.
by apply Rmin_l.
eapply (Hd2 y), ball_le, Hy.
by apply Rmin_r.
by apply Hmult.
simpl => [[y1 y2]] /=.
reflexivity.
simpl => y.
rewrite /scal /=.
rewrite mult_assoc (Hmult (f x)) -!mult_assoc.
Admitted.

Lemma filterdiff_pow_n {K : AbsRing} (x : K) (n : nat) : (forall a b : K, mult a b = mult b a) -> filterdiff (fun y : K => pow_n y n) (locally x) (fun y : K => scal y (mult (nat_to_ring n) (pow_n x (pred n)))).
Proof.
intros Hmult.
rewrite -/(is_derive (fun y : K => pow_n y n) x (mult (nat_to_ring n) (pow_n x (pred n)))).
elim: n => [ | n IH] /=.
evar_last.
apply is_derive_const.
by rewrite nat_to_ring_O mult_zero_l.
evar_last.
eapply is_derive_mult.
apply is_derive_id.
apply IH.
by apply Hmult.
simpl.
rewrite nat_to_ring_Sn mult_one_l mult_assoc (Hmult x) -mult_assoc.
rewrite mult_distr_r mult_one_l plus_comm.
apply f_equal2 => //.
clear ; case: n => [ | n] //=.
Admitted.

Lemma is_derive_n_pow_smalli: forall i p x, (i <= p)%nat -> is_derive_n (fun x : R => x ^ p) i x (INR (fact p) / INR (fact (p - i)%nat) * x ^ (p - i)%nat).
Proof.
elim => /= [ | i IH] p x Hip.
rewrite -minus_n_O ; field.
by apply INR_fact_neq_0.
eapply is_derive_ext.
intros t.
apply sym_equal, is_derive_n_unique, IH.
eapply le_trans, Hip ; by apply le_n_Sn.
evar_last.
apply is_derive_scal, is_derive_pow, is_derive_id.
rewrite MyNat.sub_succ_r.
change one with 1.
rewrite {1 2} (S_pred (p - i) O) /fact -/fact ?mult_INR.
field.
split.
apply INR_fact_neq_0.
apply not_0_INR, sym_not_eq, O_S.
Admitted.

Lemma is_derive_n_pow_bigi: forall i p x, (p < i) %nat -> is_derive_n (fun x : R => x ^ p) i x 0.
Proof.
elim => /= [ | i IH] p x Hip.
by apply lt_n_O in Hip.
apply lt_n_Sm_le, le_lt_eq_dec in Hip.
case: Hip => [Hip | ->] ; eapply is_derive_ext.
intros t ; by apply sym_equal, is_derive_n_unique, IH.
apply @is_derive_const.
intros t ; rewrite Derive_n_pow_smalli.
by rewrite minus_diag /=.
by apply le_refl.
Admitted.

Lemma Derive_n_pow_bigi: forall i p x, (p < i) %nat -> Derive_n (fun x : R => x ^ p) i x = 0.
Proof.
intros.
Admitted.

Lemma Derive_n_pow i p x: Derive_n (fun x : R => x ^ p) i x = match (le_dec i p) with | left _ => INR (fact p) / INR (fact (p -i)%nat) * x ^ (p - i)%nat | right _ => 0 end.
Proof.
case: le_dec => H.
by apply Derive_n_pow_smalli.
Admitted.

Lemma ex_derive_n_pow i p x: ex_derive_n (fun x : R => x ^ p) i x.
Proof.
case: i => //= i.
exists (Derive_n (fun x : R => x ^ p) (S i) x).
rewrite Derive_n_pow.
case: le_dec => Hip.
by apply (is_derive_n_pow_smalli (S i)).
Admitted.

Lemma is_RInt_pow : forall a b n, is_RInt (fun x => pow x n) a b (pow b (S n) / INR (S n) - pow a (S n) / INR (S n)).
Proof.
intros a b n.
set f := fun x => pow x (S n) / INR (S n).
fold (f a) (f b).
assert (H: forall x : R, is_derive f x (pow x n)).
intros x.
evar_last.
rewrite /f /Rdiv -[Rmult]/(scal (V := R_NormedModule)).
apply is_derive_scal_l.
apply is_derive_pow, is_derive_id.
rewrite /pred.
set k := INR (S n).
rewrite /scal /= /mult /one /=.
field.
rewrite /k S_INR.
apply Rgt_not_eq, INRp1_pos.
apply: is_RInt_derive => x Hx //.
apply continuity_pt_filterlim.
apply derivable_continuous_pt.
Admitted.

Lemma exp_ge_taylor (x : R) (n : nat) : 0 <= x -> sum_f_R0 (fun k => x^k / INR (fact k)) n <= exp x.
Proof.
move => Hx.
rewrite /exp /exist_exp.
case: Alembert_C3 => /= y Hy.
apply Rnot_lt_le => H.
apply Rminus_lt_0 in H.
case: (Hy _ H) => N {Hy} Hy.
move: (Hy _ (le_plus_r n N)) => {Hy}.
apply Rle_not_lt.
apply Rle_trans with (2 := Rle_abs _).
apply Rplus_le_compat_r.
elim: N => [ | N IH].
rewrite plus_0_r.
apply Req_le.
elim: (n) => {n H} [ | n /= <-].
apply Rmult_comm.
apply f_equal.
apply Rmult_comm.
apply Rle_trans with (1 := IH).
rewrite -plus_n_Sm.
move: (n + N)%nat => {n H N IH} n.
rewrite /sum_f_R0 -/sum_f_R0.
apply Rminus_le_0 ; ring_simplify.
apply Rmult_le_pos.
apply Rlt_le, Rinv_0_lt_compat, INR_fact_lt_0.
Admitted.

Lemma is_exp_Reals (x : R) : is_pseries (fun n => / INR (fact n)) x (exp x).
Proof.
rewrite /exp.
case: exist_exp => l /= Hl.
apply Series.is_series_Reals in Hl.
move: Hl ; apply Series.is_series_ext => n.
Admitted.

Lemma exp_Reals (x : R) : exp x = PSeries (fun n => / INR (fact n)) x.
Proof.
apply sym_eq, is_pseries_unique.
Admitted.

Lemma is_lim_exp_p : is_lim (fun y => exp y) p_infty p_infty.
Proof.
apply is_lim_le_p_loc with (fun y => 1 + y).
exists 0 => y Hy.
by apply Rlt_le, exp_ineq1.
pattern p_infty at 2.
replace p_infty with (Rbar_plus 1 p_infty) by auto.
eapply is_lim_plus.
apply is_lim_const.
apply is_lim_id.
Admitted.

Lemma is_lim_exp_m : is_lim (fun y => exp y) m_infty 0.
Proof.
evar_last.
apply is_lim_ext with (fun y => /(exp (- y))).
move => y ; rewrite exp_Ropp ; apply Rinv_involutive.
apply Rgt_not_eq, exp_pos.
apply is_lim_inv.
apply is_lim_comp with p_infty.
apply is_lim_exp_p.
replace p_infty with (Rbar_opp m_infty) by auto.
apply is_lim_opp.
apply is_lim_id.
by apply filter_forall.
by [].
Admitted.

Lemma Derive_n_pow_smalli: forall i p x, (i <= p)%nat -> Derive_n (fun x : R => x ^ p) i x = INR (fact p) / INR (fact (p - i)%nat) * x ^ (p - i)%nat.
Proof.
intros.
now apply is_derive_n_unique, is_derive_n_pow_smalli.
