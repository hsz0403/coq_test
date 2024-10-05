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

Lemma is_lim_div_ln_p : is_lim (fun y => ln y / y) p_infty 0.
Proof.
have H : forall x, 0 < x -> ln x < x.
move => x Hx.
apply Rminus_lt_0.
apply Rlt_le_trans with (1 := Rlt_0_1).
case: (MVT_gen (fun y => y - ln y) 1 x (fun y => (y-1)/y)).
move => z Hz.
evar (l : R).
replace ((z - 1) / z) with l.
apply is_derive_Reals.
apply derivable_pt_lim_minus.
apply derivable_pt_lim_id.
apply derivable_pt_lim_ln.
eapply Rlt_trans, Hz.
apply Rmin_case => //.
by apply Rlt_0_1.
rewrite /l ; field.
apply Rgt_not_eq ; eapply Rlt_trans, Hz.
apply Rmin_case => //.
by apply Rlt_0_1.
move => y Hy.
apply continuity_pt_minus.
apply continuity_pt_id.
apply derivable_continuous_pt ; eexists ; apply derivable_pt_lim_ln.
eapply Rlt_le_trans, Hy.
apply Rmin_case => //.
by apply Rlt_0_1.
move => c [Hc H0].
replace 1 with (1 - ln 1) by (rewrite ln_1 Rminus_0_r //).
apply Rminus_le_0.
rewrite H0.
move: Hc ; rewrite /Rmin /Rmax ; case: Rle_dec => H1 Hc.
apply Rmult_le_pos.
apply Rdiv_le_0_compat.
apply -> Rminus_le_0 ; apply Hc.
apply Rlt_le_trans with (1 := Rlt_0_1).
by apply Hc.
apply -> Rminus_le_0 ; apply H1.
apply Rnot_le_lt in H1.
replace ((c - 1) / c * (x - 1)) with ((1-c) * (1-x) / c).
apply Rdiv_le_0_compat.
apply Rmult_le_pos.
apply -> Rminus_le_0 ; apply Hc.
apply -> Rminus_le_0 ; apply Rlt_le, H1.
apply Rlt_le_trans with (1 := Hx).
by apply Hc.
field.
apply Rgt_not_eq.
apply Rlt_le_trans with (1 := Hx).
by apply Hc.
apply (is_lim_le_le_loc (fun _ => 0) (fun y => 2/sqrt y)).
exists 1 => x Hx.
split.
apply Rdiv_le_0_compat.
rewrite -ln_1.
apply ln_le.
apply Rlt_0_1.
by apply Rlt_le.
by apply Rlt_trans with (1 := Rlt_0_1).
replace (ln _) with (2 * ln (sqrt x)).
rewrite /Rdiv Rmult_assoc.
apply Rmult_le_compat_l.
apply Rlt_le, Rlt_0_2.
apply Rle_div_l.
by apply Rlt_trans with (1 := Rlt_0_1).
rewrite -{3}(sqrt_sqrt x).
field_simplify ; rewrite ?Rdiv_1.
apply Rlt_le, H.
apply sqrt_lt_R0.
by apply Rlt_trans with (1 := Rlt_0_1).
apply Rgt_not_eq.
apply sqrt_lt_R0.
by apply Rlt_trans with (1 := Rlt_0_1).
apply Rlt_le.
by apply Rlt_trans with (1 := Rlt_0_1).
change 2 with (INR 2).
rewrite -ln_pow.
rewrite /= Rmult_1_r.
rewrite sqrt_sqrt.
by [].
apply Rlt_le.
by apply Rlt_trans with (1 := Rlt_0_1).
apply sqrt_lt_R0.
by apply Rlt_trans with (1 := Rlt_0_1).
apply is_lim_const.
evar_last.
apply is_lim_div.
apply is_lim_const.
apply filterlim_sqrt_p.
by [].
by [].
simpl ; by rewrite Rmult_0_r.
