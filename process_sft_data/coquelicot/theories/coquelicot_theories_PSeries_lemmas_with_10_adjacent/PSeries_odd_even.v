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

Lemma PSeries_decr_1_aux (a : nat -> R) (x : R) : a O = 0 -> (PSeries a x) = x * PSeries (PS_decr_1 a) x.
Proof.
intros Ha0.
rewrite -PSeries_incr_1.
rewrite /PS_incr_1 /PS_decr_1 /=.
apply Series_ext.
case => //=.
Admitted.

Lemma PSeries_decr_n (a : nat -> R) (n : nat) (x : R) : ex_pseries a x -> PSeries a x = sum_f_R0 (fun k => a k * x^k) n + x^(S n) * PSeries (PS_decr_n a (S n)) x.
Proof.
intros Ha.
case: (Req_dec x 0) => Hx.
rewrite Hx PSeries_0 ; simpl ; ring_simplify.
elim: n => /= [ | n IH].
ring.
rewrite -IH ; ring.
assert (V:(pow_n x (S n) <> 0)).
rewrite pow_n_pow; now apply pow_nonzero.
move: (is_pseries_decr_n a (S n) x (/x) (PSeries a x) (Rinv_l x Hx) (lt_0_Sn _) (PSeries_correct _ _ Ha)) => Hb.
rewrite (is_pseries_unique _ _ _ Hb).
rewrite (sum_n_ext _ (fun k : nat => a k * x ^ k)).
rewrite sum_n_Reals.
replace (S n -1)%nat with n.
rewrite /scal /plus /opp /= /mult /=.
rewrite pow_n_pow -Rinv_pow ; try assumption.
field.
split; try assumption.
now apply pow_nonzero.
now apply plus_minus.
intros m; rewrite pow_n_pow.
Admitted.

Lemma PSeries_decr_n_aux (a : nat -> R) (n : nat) (x : R) : (forall k : nat, (k < n)%nat -> a k = 0) -> PSeries a x = x^n * PSeries (PS_decr_n a n) x.
Proof.
elim: n => /= [ | n IH] Ha.
rewrite Rmult_1_l.
apply PSeries_ext => n ; by intuition.
rewrite IH.
rewrite PSeries_decr_1_aux.
rewrite (Rmult_comm _ (x^n)) Rmult_assoc.
repeat apply Rmult_eq_compat_l.
apply PSeries_ext => k ; rewrite /PS_decr_1 /PS_decr_n ; by intuition.
apply Ha ; by intuition.
move => k Hk.
Admitted.

Lemma CV_radius_incr_1 (a : nat -> R) : CV_radius (PS_incr_1 a) = CV_radius a.
Proof.
assert (Ha := CV_radius_bounded a).
assert (Ha' := CV_radius_bounded (PS_incr_1 a)).
apply Rbar_le_antisym.
apply Ha' => x [M Hx] ; apply Ha.
move: (fun n => Hx (S n)) => {Hx} Hx ; simpl in Hx.
case: (Req_dec x 0) => Hx0.
rewrite Hx0 ; exists (Rabs (a O)) ; case => /= [ | n].
rewrite Rmult_1_r ; by right.
rewrite Rmult_0_l Rmult_0_r Rabs_R0.
by apply Rabs_pos.
exists (M / Rabs x) => n.
apply Rle_div_r.
by apply Rabs_pos_lt.
by rewrite -Rabs_mult Rmult_assoc (Rmult_comm _ x).
apply Ha => x [M Hx] ; apply Ha'.
exists (M * Rabs x) ; case => [ | n] /=.
rewrite Rmult_0_l Rabs_R0.
apply Rmult_le_pos.
eapply Rle_trans, (Hx O).
by apply Rabs_pos.
by apply Rabs_pos.
rewrite (Rmult_comm x) -Rmult_assoc Rabs_mult.
apply Rmult_le_compat_r.
by apply Rabs_pos.
Admitted.

Lemma CV_radius_decr_1 (a : nat -> R) : CV_radius (PS_decr_1 a) = CV_radius a.
Proof.
assert (Ha := CV_radius_bounded a).
assert (Ha' := CV_radius_bounded (PS_decr_1 a)).
apply Rbar_le_antisym.
apply Ha' => x [M Hx] ; apply Ha.
eexists ; case => [ | n] ; simpl.
eapply Rle_trans, Rmax_l.
rewrite Rmult_1_r ; apply Rle_refl.
eapply Rle_trans, Rmax_r.
rewrite (Rmult_comm x) -Rmult_assoc Rabs_mult.
apply Rmult_le_compat_r.
by apply Rabs_pos.
by apply Hx.
apply Ha => x [M Hx] ; apply Ha'.
move: (fun n => Hx (S n)) => {Hx} Hx ; simpl in Hx.
case: (Req_dec x 0) => Hx0.
rewrite Hx0 ; exists (Rabs (a 1%nat)) ; case => /= [ | n].
rewrite Rmult_1_r ; by right.
rewrite Rmult_0_l Rmult_0_r Rabs_R0.
by apply Rabs_pos.
exists (M / Rabs x) => n.
apply Rle_div_r.
by apply Rabs_pos_lt.
rewrite -Rabs_mult Rmult_assoc (Rmult_comm _ x).
Admitted.

Lemma is_pseries_mult (a b : nat -> R) (x la lb : R) : is_pseries a x la -> is_pseries b x lb -> Rbar_lt (Rabs x) (CV_radius a) -> Rbar_lt (Rabs x) (CV_radius b) -> is_pseries (PS_mult a b) x (la * lb).
Proof.
move => Hla Hlb Ha Hb.
apply is_series_ext with (fun n => sum_f_R0 (fun k => (fun l => a l * x ^ l) k * (fun l => b l * x ^ l) (n - k)%nat) n).
move => n.
rewrite /PS_mult /scal /= /mult /= scal_sum.
apply sum_eq => i Hi.
rewrite -{4}(MyNat.sub_add _ _ Hi).
rewrite pow_n_pow pow_add.
ring.
apply (is_series_mult (fun l => a l * x ^ l) (fun l => b l * x ^ l)).
now apply (is_pseries_R a x la).
now apply (is_pseries_R b x lb).
by apply CV_disk_inside.
Admitted.

Lemma ex_pseries_mult (a b : nat -> R) (x : R) : Rbar_lt (Rabs x) (CV_radius a) -> Rbar_lt (Rabs x) (CV_radius b) -> ex_pseries (PS_mult a b) x.
Proof.
move => Ha Hb.
exists ((PSeries a x) * (PSeries b x)).
Admitted.

Lemma PSeries_mult (a b : nat -> R) (x : R) : Rbar_lt (Rabs x) (CV_radius a) -> Rbar_lt (Rabs x) (CV_radius b) -> PSeries (PS_mult a b) x = PSeries a x * PSeries b x.
Proof.
move => Ha Hb.
apply is_pseries_unique.
Admitted.

Lemma is_pseries_odd_even (a : nat -> R) (x l1 l2 : R) : is_pseries (fun n => a (2*n)%nat) (x^2) l1 -> is_pseries (fun n => a (2*n+1)%nat) (x^2) l2 -> is_pseries a x (l1 + x * l2).
Proof.
rewrite 3!is_pseries_R.
move => H1 H2.
apply filterlim_ext with (fun n => (sum_n (fun k : nat => a (2 * k)%nat * (x ^ 2) ^ k) (div2 n)) + x * match n with | O => 0 | S n => (sum_n (fun k : nat => a (2 * k + 1)%nat * (x ^ 2) ^ k) (div2 n)) end).
case => [ | n].
rewrite /= !sum_O /= ; ring.
case: (even_odd_dec n) => Hn.
rewrite 3!sum_n_Reals.
rewrite -(even_div2 _ Hn) {3}(even_double _ Hn).
elim: (div2 n) => {n Hn} [ | n] ; rewrite ?double_S /sum_f_R0 -/sum_f_R0.
rewrite /double /= ; ring.
rewrite -pow_mult.
replace (2 * S n)%nat with (S (S (double n))) by (rewrite -double_S /double ; ring).
replace (S (S (double n)) + 1)%nat with (S (S (S (double n)))) by ring.
move => <- ; simpl ; ring.
rewrite 3!sum_n_Reals.
rewrite -(odd_div2 _ Hn) {3}(odd_double _ Hn).
elim: (div2 n) => {n Hn} [ | n] ; rewrite ?double_S /sum_f_R0 -/sum_f_R0.
rewrite /double /= ; ring.
rewrite -?pow_mult.
replace (2 * S n)%nat with (S (S (double n))) by (rewrite -double_S /double ; ring).
replace (2 * S (S n))%nat with (S (S (S (S (double n))))) by (rewrite -double_S /double ; ring).
replace (S (S (double n)) + 1)%nat with (S (S (S (double n)))) by ring.
move => <- ; simpl ; ring.
apply (is_lim_seq_plus' _ _ l1 (x*l2)).
apply filterlim_comp with (2:=H1).
intros P [N HN].
exists (2*N+1)%nat.
intros n Hn; apply HN.
apply le_double.
apply plus_le_reg_l with 1%nat.
rewrite Plus.plus_comm.
apply le_trans with (1:=Hn).
apply le_trans with (1+double (div2 n))%nat.
case (even_or_odd n); intros J.
rewrite <- even_double; try exact J.
now apply le_S.
rewrite <- odd_double; easy.
simpl; now rewrite plus_0_r.
apply (is_lim_seq_scal_l _ x l2) => //.
apply filterlim_ext_loc with (fun n => sum_n (fun k : nat => a (2 * k + 1)%nat * (x ^ 2) ^ k) (div2 (pred n))).
exists 1%nat; intros y; case y.
easy.
intros n _; reflexivity.
apply filterlim_comp with (2:=H2).
intros P [N HN].
exists (2*N+2)%nat.
intros n Hn; apply HN.
apply le_double.
apply plus_le_reg_l with 2%nat.
rewrite Plus.plus_comm.
apply le_trans with (1:=Hn).
apply le_trans with (1+(1+double (div2 (pred n))))%nat.
case (even_or_odd (pred n)); intros J.
rewrite <- even_double; try exact J.
case n.
simpl; now apply le_S, le_S.
intros m; simpl; now apply le_S.
rewrite <- odd_double; try exact J.
case n; simpl; try easy.
now apply le_S.
Admitted.

Lemma ex_pseries_odd_even (a : nat -> R) (x : R) : ex_pseries (fun n => a (2*n)%nat) (x^2) -> ex_pseries (fun n => a (2*n+1)%nat) (x^2) -> ex_pseries a x.
Proof.
move => [l1 H1] [l2 H2].
exists (l1 + x * l2).
Admitted.

Lemma PSeries_const_0 : forall x, PSeries (fun _ => 0) x = 0.
Proof.
move => x.
replace 0 with (real 0) by auto.
apply (f_equal real).
rewrite -{2}(Lim_seq_const 0) /=.
apply Lim_seq_ext.
elim => /= [ | n IH].
rewrite sum_O ; ring.
Admitted.

Lemma CV_radius_const_0 : CV_radius (fun _ => 0) = p_infty.
Proof.
suff : forall x, Rbar_le (Rabs x) (CV_radius (fun _ : nat => 0)).
case H : (CV_radius (fun _ : nat => 0)) => [cv | | ] //= H0.
case: (Rle_lt_dec 0 cv) => Hcv.
move: (H0 (cv + 1)) => {H0} H0.
contradict H0 ; apply Rlt_not_le => /=.
apply Rlt_le_trans with (2 := Rle_abs _).
apply Rminus_lt_0 ; ring_simplify ; by apply Rlt_0_1.
contradict Hcv ; apply (Rbar_le_not_lt cv 0).
rewrite -Rabs_R0.
by apply H0.
move: (H0 0) => {H0} H0.
contradict H0 ; by apply Rbar_lt_not_le.
move => x ; apply Rbar_not_lt_le => Hx.
apply CV_disk_outside in Hx.
apply: Hx.
apply is_lim_seq_ext with (fun _ => 0).
move => n ; ring.
Admitted.

Lemma is_pseries_opp (a : nat -> V) (x :K) (l : V) : is_pseries a x l -> is_pseries (PS_opp a) x (opp l).
Proof.
intros H.
replace (opp l) with (scal (opp (one : K)) l).
2: now rewrite scal_opp_l scal_one.
apply is_pseries_ext with (PS_scal (opp one) a).
intros n; unfold PS_scal, PS_opp.
now rewrite scal_opp_l scal_one.
apply is_pseries_scal.
rewrite -opp_mult_l -opp_mult_r.
by rewrite mult_one_l mult_one_r.
Admitted.

Lemma ex_pseries_opp (a : nat -> V) (x : K) : ex_pseries a x -> ex_pseries (PS_opp a) x.
Proof.
intros [l Hl].
exists (opp l).
Admitted.

Lemma PSeries_opp (a : nat -> R) (x : R) : PSeries (PS_opp a) x = - PSeries a x.
Proof.
replace (- PSeries a x) with ((-1) * PSeries a x) by ring.
rewrite -PSeries_scal.
apply PSeries_ext => n.
Admitted.

Lemma CV_radius_opp (a : nat -> R) : (CV_radius (PS_opp a)) = (CV_radius a).
Proof.
rewrite -(CV_radius_scal (-1)).
apply CV_radius_ext => n.
by rewrite /PS_scal /PS_opp scal_opp_l scal_opp_r opp_opp scal_one.
Admitted.

Lemma is_pseries_minus (a b : nat -> V) (x:K) (la lb : V) : is_pseries a x la -> is_pseries b x lb -> is_pseries (PS_minus a b) x (plus la (opp lb)).
Proof.
move => Ha Hb.
apply is_pseries_plus.
exact: Ha.
Admitted.

Lemma ex_pseries_minus (a b : nat -> V) (x : K) : ex_pseries a x -> ex_pseries b x -> ex_pseries (PS_minus a b) x.
Proof.
move => Ha Hb.
apply ex_pseries_plus.
exact: Ha.
Admitted.

Lemma PSeries_minus (a b : nat -> R) (x : R) : ex_pseries a x -> ex_pseries b x -> PSeries (PS_minus a b) x = PSeries a x - PSeries b x.
Proof.
move => Ha Hb.
rewrite PSeries_plus.
by rewrite PSeries_opp.
exact: Ha.
Admitted.

Lemma Abel (a : nat -> R) : Rbar_lt 0 (CV_radius a) -> Rbar_lt (CV_radius a) p_infty -> ex_pseries a (CV_radius a) -> filterlim (PSeries a) (at_left (CV_radius a)) (locally (PSeries a (CV_radius a))).
Proof.
case Hcv : (CV_radius a) => [cv | | ] //= Hcv0 _ Ha1.
wlog: cv a Hcv Hcv0 Ha1 / (cv = 1) => Hw.
apply filterlim_ext with (fun x => PSeries (fun n => a n * cv ^ n) (x / cv)).
intros x.
apply Series_ext => n.
rewrite Rmult_assoc -Rpow_mult_distr.
apply f_equal, f_equal2 => //.
field ; by apply Rgt_not_eq.
apply filterlim_comp with (at_left 1).
intros P [d Hd].
unfold filtermap.
eapply filter_imp.
intros x Hx ; apply Hd.
apply @norm_compat1.
rewrite /minus /plus /opp /=.
replace (x / cv + _) with ((x - cv) / cv) by (field ; exact: Rgt_not_eq).
rewrite /norm /= /abs /= Rabs_div ; try by apply Rgt_not_eq.
rewrite (Rabs_pos_eq cv) ; try by apply Rlt_le.
apply Rlt_div_l => //.
eapply (proj1 Hx).
apply Rlt_div_l => //.
rewrite Rmult_1_l.
by apply (proj2 Hx).
assert (Hd' : 0 < d * cv).
apply Rmult_lt_0_compat.
by apply d.
by [].
exists (mkposreal _ Hd') => /= y Hy Hy0 ; by split.
replace (PSeries a cv) with (PSeries (fun n : nat => a n * cv ^ n) 1).
apply (Hw 1 (fun n : nat => a n * cv ^ n)) ; clear Hw.
apply Rbar_le_antisym.
move: Hcv ; rewrite /CV_radius /Lub.Lub_Rbar /CV_disk.
case: Lub.ex_lub_Rbar => l /= Hl Hl1 ; case: Lub.ex_lub_Rbar => l' /= Hl'.
rewrite Hl1 in Hl => {l Hl1}.
apply Hl'.
intros x Hx.
apply (Rmult_le_reg_l cv) => //.
rewrite Rmult_1_r.
apply Hl.
move: Hx ; apply ex_series_ext => n.
by rewrite Rpow_mult_distr Rmult_assoc.
rewrite -Rabs_R1.
apply Rbar_not_lt_le => Hcv'.
apply CV_disk_outside in Hcv'.
apply: Hcv'.
apply ex_series_lim_0 ; move: Ha1 ; apply ex_series_ext => n.
rewrite pow_n_pow pow1 Rmult_1_r.
apply Rmult_comm.
by apply Rlt_0_1.
move: Ha1 ; apply ex_series_ext => n.
rewrite !pow_n_pow pow1 scal_one.
apply Rmult_comm.
by [].
apply Series_ext => n.
by rewrite pow1 Rmult_1_r.
rewrite Hw in Hcv Ha1 |- * => {cv Hw Hcv0}.
wlog: a Hcv Ha1 / (PSeries a 1 = 0) => Hw.
set b := fun n => match n with | O => a O - PSeries a 1 | S n => a (S n) end.
assert (CV_radius b = Finite 1).
rewrite -Hcv.
rewrite -(CV_radius_decr_1 a) -(CV_radius_decr_1 b).
apply CV_radius_ext => n.
reflexivity.
assert (ex_pseries b 1).
apply ex_series_incr_1.
apply ex_series_incr_1 in Ha1.
move: Ha1 ; apply ex_series_ext => n.
reflexivity.
assert (PSeries b 1 = 0).
rewrite PSeries_decr_1 //.
rewrite /b PSeries_decr_1 /PS_decr_1 //.
ring.
specialize (Hw b H H0 H1).
apply filterlim_ext_loc with (fun x => PSeries b x + PSeries a 1).
exists (mkposreal _ Rlt_0_1) => x Hx0 Hx.
apply (Rabs_lt_between' x 1 1) in Hx0.
rewrite Rminus_eq_0 in Hx0.
rewrite PSeries_decr_1.
rewrite /b (PSeries_decr_1 a x) /PS_decr_1.
ring.
apply CV_radius_inside.
rewrite Hcv Rabs_pos_eq.
by [].
by apply Rlt_le, Hx0.
apply CV_radius_inside.
rewrite H Rabs_pos_eq.
by [].
by apply Rlt_le, Hx0.
rewrite -{2}(Rplus_0_l (PSeries a 1)).
eapply filterlim_comp_2.
by apply Hw.
by apply filterlim_const.
rewrite H1.
apply @filterlim_plus.
apply PSeries_correct in Ha1.
rewrite Hw in Ha1 |- * => {Hw}.
set Sa := sum_n a.
assert (forall n x, sum_n (fun k => scal (pow_n x k) (a k)) n = (1 - x) * sum_n (fun k => scal (pow_n x k) (Sa k)) n + scal (pow_n x (S n)) (Sa n)).
elim => /= [ | n IH] x.
rewrite /Sa !sum_O scal_one mult_one_r /=.
rewrite /scal /= /mult /= ; ring.
rewrite !sum_Sn IH ; clear IH.
rewrite /Sa /= !sum_Sn -/(Sa n).
rewrite /plus /scal /= /mult /=.
ring.
assert (forall x, Rabs x < 1 -> is_pseries Sa x (PSeries a x / (1 - x))).
intros x Hx.
destruct (CV_radius_inside a x) as [l Hl].
rewrite Hcv.
by apply Hx.
rewrite (is_pseries_unique _ _ _ Hl).
rewrite /is_pseries /is_series.
replace (@locally R_NormedModule (l / (1 - x))) with (Rbar_locally (Rbar_mult (l - ((Rbar_mult x 0) * 0)) (/ (1 - x)))).
apply (is_lim_seq_ext (fun n => (sum_n (fun k : nat => scal (pow_n (K := R_AbsRing) x k) (a k)) n - scal (pow_n (K := R_AbsRing) x (S n)) (Sa n)) / (1 - x)) (sum_n (fun k : nat => scal (pow_n (K := R_AbsRing) x k) (Sa k)))).
intros n ; rewrite H.
field.
apply Rgt_not_eq ; apply -> Rminus_lt_0.
by apply Rabs_lt_between, Hx.
apply is_lim_seq_scal_r.
apply is_lim_seq_minus'.
apply Hl.
apply is_lim_seq_mult'.
apply is_lim_seq_mult'.
apply is_lim_seq_const.
eapply is_lim_seq_ext.
intros n ; by apply sym_eq, pow_n_pow.
apply is_lim_seq_geom.
by apply Hx.
move: Ha1 ; apply (is_lim_seq_ext _ _ 0).
intros n ; apply sum_n_ext => k.
by rewrite pow_n_pow pow1 scal_one.
by replace (Rbar_mult (l - Rbar_mult x 0 * 0) (/ (1 - x))) with (Finite (l / (1 - x))) by (simpl ; apply f_equal ; unfold Rdiv ; ring).
apply filterlim_ext_loc with (fun x => (1-x) * PSeries Sa x).
exists (mkposreal _ Rlt_0_1) ; simpl ; intros x Hx Hx1.
apply (Rabs_lt_between' x 1 1) in Hx.
rewrite Rminus_eq_0 in Hx.
assert (Rabs x < 1).
rewrite Rabs_pos_eq.
by apply Hx1.
by apply Rlt_le, Hx.
specialize (H0 x H1).
rewrite (is_pseries_unique _ _ _ H0).
field.
by apply Rgt_not_eq ; apply -> Rminus_lt_0.
apply filterlim_locally => eps.
destruct (Ha1 (ball 0 (pos_div_2 eps))) as [N HN].
apply locally_ball.
eapply filter_imp.
intros x Hx.
rewrite (PSeries_decr_n _ N).
rewrite (double_var eps) Rmult_plus_distr_l.
eapply Rle_lt_trans.
rewrite /minus opp_zero plus_zero_r.
apply @abs_triangle.
rewrite /abs /= 3!Rabs_mult.
apply Rplus_lt_le_compat.
eapply Rle_lt_trans.
apply Rmult_le_compat_l.
by apply Rabs_pos.
eapply Rle_trans.
apply Rsum_abs.
apply sum_growing.
intros n.
rewrite Rabs_mult.
apply Rmult_le_compat_l.
by apply Rabs_pos.
rewrite -RPow_abs.
apply pow_incr ; split.
apply Rabs_pos.
apply Rlt_le.
instantiate (1 := 1).
eapply (proj1 Hx).
destruct Hx as [Hx1 Hx].
eapply Rle_lt_trans.
apply Rmult_le_compat_l.
by apply Rabs_pos.
apply (Rmax_r 1).
apply Rlt_div_r.
eapply Rlt_le_trans, Rmax_l.
by apply Rlt_0_1.
eapply (proj1 Hx).
destruct Hx as [Hx1 [Hx2 Hx]].
eapply Rle_trans.
apply Rmult_le_compat_l.
by apply Rabs_pos.
apply Rmult_le_compat ; try by apply Rabs_pos.
rewrite -/(pow _ (S N)) -RPow_abs.
apply pow_incr ; split.
apply Rabs_pos.
apply Rlt_le, Hx1.
eapply Rle_trans.
apply Series_Rabs.
eapply @ex_series_le.
intros n ; rewrite /norm /= /abs /= Rabs_Rabsolu.
rewrite Rabs_mult.
rewrite -RPow_abs.
apply Rmult_le_compat_r.
rewrite RPow_abs ; by apply Rabs_pos.
rewrite /PS_decr_n.
eapply Rle_trans, Rlt_le, HN.
apply Req_le, f_equal.
rewrite /minus opp_zero plus_zero_r.
apply sum_n_ext => k.
by rewrite pow_n_pow pow1 scal_one.
apply le_trans with (1 := le_n_Sn _).
apply le_plus_l.
apply @ex_series_scal.
apply ex_series_geom.
by rewrite Rabs_Rabsolu.
apply Series_le.
intros n ; split.
apply Rabs_pos.
rewrite Rabs_mult.
rewrite -RPow_abs.
apply Rmult_le_compat_r.
rewrite RPow_abs ; by apply Rabs_pos.
rewrite /PS_decr_n.
eapply Rle_trans, Rlt_le, HN.
apply Req_le, f_equal.
rewrite /minus opp_zero plus_zero_r.
apply sum_n_ext => k.
by rewrite pow_n_pow pow1 scal_one.
apply le_trans with (1 := le_n_Sn _).
apply le_plus_l.
apply @ex_series_scal.
apply ex_series_geom.
by rewrite Rabs_Rabsolu.
rewrite Series_scal_l Series_geom.
rewrite pow1 Rmult_1_l !Rabs_pos_eq.
apply Req_le ; simpl ; field.
apply Rgt_not_eq ; apply -> Rminus_lt_0.
eapply Rle_lt_trans, Hx1.
by apply Rle_abs.
apply Hx.
apply -> Rminus_le_0.
eapply Rle_trans, Rlt_le, Hx1.
by apply Rle_abs.
by rewrite Rabs_Rabsolu.
eexists ; apply H0, Hx.
assert (0 < Rmin (eps / 2 / Rmax 1 (sum_f_R0 (fun n : nat => Rabs (Sa n) * 1 ^ n) N)) 1).
apply Rmin_case.
apply Rdiv_lt_0_compat.
by apply is_pos_div_2.
eapply Rlt_le_trans, Rmax_l.
by apply Rlt_0_1.
by apply Rlt_0_1.
exists (mkposreal _ H1) => /= y Hy Hy1.
split.
apply (Rabs_lt_between' y 1 (Rmin (eps / 2 / Rmax 1 (sum_f_R0 (fun n : nat => Rabs (Sa n) * 1 ^ n) N)) 1)) in Hy.
rewrite {1}/Rminus -Rmax_opp_Rmin Rplus_max_distr_l Rplus_min_distr_l in Hy.
rewrite -!/(Rminus _ _) Rminus_eq_0 in Hy.
rewrite Rabs_pos_eq.
by [].
apply Rlt_le.
eapply Rle_lt_trans, Hy.
by apply Rmax_r.
split.
eapply Rlt_le_trans.
rewrite -Rabs_Ropp Ropp_minus_distr'.
apply Hy.
by apply Rmin_l.
apply (Rabs_lt_between' y 1 (Rmin (eps / 2 / Rmax 1 (sum_f_R0 (fun n : nat => Rabs (Sa n) * 1 ^ n) N)) 1)) in Hy.
rewrite {1}/Rminus -Rmax_opp_Rmin Rplus_max_distr_l Rplus_min_distr_l in Hy.
rewrite -!/(Rminus _ _) Rminus_eq_0 in Hy.
eapply Rle_trans, Rlt_le, Hy.
Admitted.

Lemma PSeries_odd_even (a : nat -> R) (x : R) : ex_pseries (fun n => a (2*n)%nat) (x^2) -> ex_pseries (fun n => a (2*n+1)%nat) (x^2) -> PSeries a x = PSeries (fun n => a (2*n)%nat) (x^2) + x * PSeries (fun n => a (2*n+1)%nat) (x^2).
Proof.
move => H1 H2 ; apply is_pseries_unique.
apply (is_pseries_odd_even a x); by apply PSeries_correct.
