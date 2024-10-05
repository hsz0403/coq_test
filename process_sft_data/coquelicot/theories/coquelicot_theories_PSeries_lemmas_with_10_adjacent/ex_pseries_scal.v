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

Lemma CV_radius_infinite_DAlembert (a : nat -> R) : (forall n:nat, a n <> 0) -> is_lim_seq (fun n:nat => Rabs (a (S n) / a n)) 0 -> CV_radius a = p_infty.
Proof.
move => Ha Hda.
rewrite /CV_radius /Lub_Rbar ; case: ex_lub_Rbar ; case => [cv | | ] //= [ub lub] ; have : False => //.
have H : CV_disk a (cv + 1).
have H : 0 < cv + 1.
apply Rlt_le_trans with (0+1).
rewrite Rplus_0_l ; by apply Rlt_0_1.
apply Rplus_le_compat_r.
apply ub.
exists (Rabs (a O)).
apply (is_lim_seq_ext (fun _ => Rabs (a O)) _ (Rabs (a 0%nat))).
elim => [ | k IH] /=.
by rewrite sum_O Rmult_1_r.
by rewrite sum_Sn /= Rmult_0_l Rmult_0_r Rabs_R0 /plus /= Rplus_0_r.
by apply is_lim_seq_const.
apply ex_series_DAlembert with 0.
by apply Rlt_0_1.
move => n ; apply Rmult_integral_contrapositive_currified.
by[].
by apply Rgt_not_eq, pow_lt.
rewrite -(Rmult_0_r (Rabs (cv + 1))).
apply (CV_disk_DAlembert_aux a (cv + 1)).
by apply Rgt_not_eq.
by [].
by [].
move: (ub (cv+1) H).
by apply Rbar_lt_not_le, Rlt_n_Sn.
case: (ub 0) => //.
exists (Rabs (a O)).
apply (is_lim_seq_ext (fun _ => Rabs (a O)) _ (Rabs (a 0%nat))).
elim => [ | k IH] /=.
by rewrite sum_O Rmult_1_r.
by rewrite sum_Sn /= Rmult_0_l Rmult_0_r Rabs_R0 /plus /= Rplus_0_r.
Admitted.

Lemma CV_radius_Reals_0 (a : nat -> R) (r : posreal) : Rbar_lt (Finite r) (CV_radius a) -> CVN_r (fun n x => a n * x ^ n) r.
Proof.
move => Hr.
rewrite /CVN_r /Boule.
have H := CV_radius_bounded a.
exists (fun n => Rabs (a n * r ^ n)).
exists (Series (fun n => Rabs (a n * r ^ n))) ; split.
rewrite -(Rabs_pos_eq r (Rlt_le _ _ (cond_pos r))) in Hr.
apply CV_disk_inside in Hr.
apply Lim_seq_correct' in Hr ; rewrite -/(Series (fun n : nat => Rabs (a n * r ^ n))) in Hr.
move => e He.
apply is_lim_seq_spec in Hr.
case: (Hr (mkposreal e He)) => /= {Hr} N Hr.
exists N => n Hn.
replace (sum_f_R0 (fun k : nat => Rabs (Rabs (a k * r ^ k))) n) with (sum_f_R0 (fun k : nat => (Rabs (a k * r ^ k))) n).
rewrite <- sum_n_Reals; by apply Hr.
elim: n {Hn} => /= [ | n IH] ; rewrite Rabs_Rabsolu.
by [].
by rewrite IH.
move => n x Hx.
rewrite ?Rabs_mult -?RPow_abs.
apply Rmult_le_compat_l.
by apply Rabs_pos.
apply pow_incr ; split.
by apply Rabs_pos.
rewrite (Rabs_pos_eq r).
rewrite Rminus_0_r in Hx.
by apply Rlt_le.
Admitted.

Lemma CV_radius_Reals_1 (a : nat -> R) (r : posreal) : CVN_r (fun n x => a n * x ^ n) r -> Rbar_le (Finite r) (CV_radius a).
Proof.
case => An [l [H H0]].
have H1 : is_lub_Rbar (CV_disk a) (CV_radius a).
rewrite /CV_radius /Lub_Rbar ; by case: ex_lub_Rbar.
have H2 : forall (y : R), 0 < y < r -> (CV_disk a y).
move => y Hy.
apply @ex_series_le with An.
move => n ; rewrite /norm /= /abs /= Rabs_Rabsolu.
apply H0 ; rewrite /Boule Rabs_pos_eq Rminus_0_r.
by apply Hy.
by apply Rlt_le, Hy.
exists l.
apply (is_lim_seq_spec _ l).
intros eps.
case: (H eps (cond_pos eps)) => N {H} H.
exists N => n Hn.
set v := sum_n _ _.
replace v with (sum_n (fun k : nat => Rabs (An k)) n).
rewrite sum_n_Reals; by apply H.
rewrite /v {v}.
elim: n {Hn} => /= [ | n IH].
rewrite !sum_O ; apply Rabs_pos_eq.
apply Rle_trans with (Rabs (a O * 0 ^ O)).
by apply Rabs_pos.
apply H0 ; rewrite /Boule Rminus_0_r Rabs_R0 ; by apply r.
rewrite !sum_Sn IH Rabs_pos_eq.
by [].
apply Rle_trans with (Rabs (a (S n) * 0 ^ (S n))).
by apply Rabs_pos.
apply H0 ; rewrite /Boule Rminus_0_r Rabs_R0 ; by apply r.
have H3 : forall y, 0 < y < r -> Rbar_le (Finite (y)) (CV_radius a).
move => y Hy.
by apply H1, H2.
have H4 := CV_radius_ge_0 a.
case: (CV_radius a) H3 H4 => /= [cv | | ] // H3 H4.
apply Rnot_lt_le => /= H5.
have H6 : 0 < (cv+r)/2 < r.
lra.
move: (H3 _ H6).
Admitted.

Lemma CV_radius_Reals_2 (a : nat -> R) (x : R) : Rbar_lt (Finite (Rabs x)) (CV_radius a) -> exists r : posreal, CVU (fun n x => sum_f_R0 (fun k => a k * x ^ k) n) (PSeries a) x r.
Proof.
move => Hx.
have H : exists r : posreal, Rabs x < r /\ Rbar_lt (Finite r) (CV_radius a).
case: (CV_radius a) Hx => /= [cv | | ] Hx.
have H : 0 < (Rabs x + cv)/2.
generalize (Rabs_pos x) ; lra.
exists (mkposreal _ H) => /=.
lra.
have H : 0 < Rabs x + 1.
apply Rle_lt_0_plus_1, Rabs_pos.
exists (mkposreal _ H) => /=.
split.
by apply Rlt_plus_1.
by [].
by [].
case: H => r H.
apply CVN_CVU_r with r.
by apply CV_radius_Reals_0, H.
Admitted.

Lemma is_pseries_plus (a b : nat -> V) (x :K) (la lb : V) : is_pseries a x la -> is_pseries b x lb -> is_pseries (PS_plus a b) x (plus la lb).
Proof.
move => Ha Hb.
apply filterlim_ext with (f:= (fun n => plus (sum_n (fun k => scal (pow_n x k) (a k)) n) (sum_n (fun k => scal (pow_n x k) (b k)) n))).
elim => [ | n IH].
simpl ; rewrite /PS_plus !sum_O.
now repeat rewrite scal_one.
simpl ; rewrite !sum_Sn -IH /PS_plus.
generalize (sum_n (fun k : nat => scal (pow_n x k) (a k)) n) => a' ; generalize (sum_n (fun k : nat => scal (pow_n x k) (b k)) n) => b'.
repeat rewrite -plus_assoc; apply f_equal.
rewrite plus_comm -plus_assoc; apply f_equal.
rewrite scal_distr_l; apply plus_comm.
Admitted.

Lemma ex_pseries_plus (a b : nat -> V) (x : K) : ex_pseries a x -> ex_pseries b x -> ex_pseries (PS_plus a b) x.
Proof.
move => [la Ha] [lb Hb].
exists (plus la lb).
Admitted.

Lemma PSeries_plus (a b : nat -> R) (x : R) : ex_pseries a x -> ex_pseries b x -> PSeries (PS_plus a b) x = PSeries a x + PSeries b x.
Proof.
intros Ha Hb.
apply is_pseries_unique.
apply: is_pseries_plus ; rewrite PSeries_eq ; apply Series_correct.
by apply Ha.
Admitted.

Lemma CV_disk_plus (a b : nat -> R) (x : R) : (CV_disk a x) -> (CV_disk b x) -> (CV_disk (PS_plus a b) x).
Proof.
move => Ha Hb.
move: (ex_series_plus _ _ Ha Hb).
apply @ex_series_le => n ; rewrite /norm /= /abs /= Rabs_Rabsolu.
rewrite Rmult_plus_distr_r.
Admitted.

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
Admitted.

Lemma is_pseries_scal (c : K) (a : nat -> V) (x : K) (l : V) : mult x c = mult c x -> is_pseries a x l -> is_pseries (PS_scal c a) x (scal c l).
Proof.
move => Hx Ha.
apply (filterlim_ext (fun n => scal c (sum_n (fun k => scal (pow_n x k) (a k)) n))).
elim => [ | n IH].
simpl ; rewrite /PS_scal.
rewrite !sum_O.
now repeat rewrite scal_one.
simpl ; rewrite !sum_Sn -IH /PS_scal.
rewrite scal_distr_l; apply f_equal.
rewrite 2! scal_assoc.
apply f_equal2.
rewrite -/(pow_n x (S n)).
clear -Hx.
elim: (S n) => {n} /= [ | n IH].
by rewrite mult_one_l mult_one_r.
by rewrite -mult_assoc -IH 2!mult_assoc Hx.
by [].
Admitted.

Lemma PSeries_scal (c : R) (a : nat -> R) (x : R) : PSeries (PS_scal c a) x = c * PSeries a x.
Proof.
rewrite -Series_scal_l.
apply Series_ext.
move => n /=.
Admitted.

Lemma CV_disk_scal (c : R) (a : nat -> R) (x : R) : (CV_disk a x) -> (CV_disk (PS_scal c a) x).
Proof.
move => Ha.
apply ex_series_ext with (fun n => Rabs c * Rabs (a n * x ^ n)).
move => n ; rewrite -Rabs_mult ; apply f_equal ; by rewrite /PS_scal /= Rmult_assoc.
apply @ex_series_scal.
Admitted.

Lemma CV_radius_scal (c : R) (a : nat -> R) : c <> 0 -> (CV_radius (PS_scal c a)) = (CV_radius a).
Proof.
rewrite /CV_radius /Lub_Rbar ; case: ex_lub_Rbar => la [ub_a lub_a] ; case: ex_lub_Rbar => lc [ub_c lub_c] /= Hc.
apply Rbar_le_antisym.
apply lub_a => x Hx.
apply ub_c.
assert (CV_disk (PS_scal (/c) (PS_scal c a)) x).
by apply CV_disk_scal.
move: H ; apply ex_series_ext => n.
apply f_equal.
rewrite /PS_scal /scal /= /mult /= ; by field.
apply lub_c => x Hx.
apply ub_a.
Admitted.

Lemma PSeries_scal_r (c : R) (a : nat -> R) (x : R) : PSeries (PS_scal_r c a) x = PSeries a x * c.
Proof.
rewrite -Series_scal_r.
apply Series_ext.
move => n /=.
Admitted.

Lemma CV_disk_scal_r (c : R) (a : nat -> R) (x : R) : (CV_disk a x) -> (CV_disk (PS_scal_r c a) x).
Proof.
move => Ha.
apply ex_series_ext with (fun n => Rabs c * Rabs (a n * x ^ n)).
move => n ; rewrite -Rabs_mult ; apply f_equal ; rewrite /PS_scal_r /= ; ring.
Admitted.

Lemma CV_radius_scal_r (c : R) (a : nat -> R) : c <> 0 -> (CV_radius (PS_scal_r c a)) = (CV_radius a).
Proof.
intros Hc.
rewrite -(CV_radius_scal c a).
apply CV_radius_ext => n.
apply Rmult_comm.
Admitted.

Lemma is_pseries_incr_1 (a : nat -> V) (x:K) (l : V) : is_pseries a x l -> is_pseries (PS_incr_1 a) x (scal x l).
Proof.
move => Ha.
apply filterlim_ext_loc with (fun n : nat => scal x (sum_n (fun k => scal (pow_n x k) (a k)) (pred n))).
exists 1%nat; intros n; case n.
intros Hn; contradict Hn ; apply lt_n_O.
clear n; intros n _ ;induction n.
now rewrite /= !sum_Sn !sum_O /= mult_one_r 2!scal_one plus_zero_l.
apply trans_eq with (plus (sum_n (fun k : nat => scal (pow_n x k) (PS_incr_1 a k)) (S n)) (scal (pow_n x (S (S n))) (PS_incr_1 a (S (S n))))).
2: rewrite /= !sum_Sn ; reflexivity.
rewrite -IHn; simpl.
rewrite !sum_Sn scal_distr_l; apply f_equal.
now rewrite scal_assoc.
apply filterlim_comp with (f:= fun n => pred n) (G:=eventually) (g:=fun n => scal x (sum_n (fun k : nat => scal (pow_n x k) (a k)) n)).
apply eventually_subseq_loc.
exists 1%nat.
intros n Hn.
rewrite -pred_Sn.
now apply lt_pred_n_n.
Admitted.

Lemma ex_pseries_incr_1 (a : nat -> V) (x : K) : ex_pseries a x -> ex_pseries (PS_incr_1 a) x.
Proof.
Admitted.

Lemma PS_incr_n_simplify (a : nat -> V) (n k : nat) : PS_incr_n a n k = match (le_lt_dec n k) with | left _ => a (k-n)%nat | right _ => zero end.
Proof.
case: le_lt_dec => H.
elim: n k H => [ | n IH] k H.
rewrite /PS_incr_n ; by case: k H.
case: k H => [ | k] H.
by apply le_Sn_0 in H.
rewrite /PS_incr_n -/PS_incr_n /PS_incr_1.
rewrite IH.
apply f_equal.
by elim: n k H {IH} => /= [ | n IH] k H.
by apply le_S_n.
elim: n k H => [ | n IH] k H.
by apply lt_n_O in H.
rewrite /PS_incr_n -/PS_incr_n /PS_incr_1.
case: k H => [ | k] H.
by [].
Admitted.

Lemma is_pseries_incr_n (a : nat -> V) (n : nat) (x : K) (l : V) : is_pseries a x l -> is_pseries (PS_incr_n a n) x (scal (pow_n x n) l).
Proof.
move => Ha.
elim: n => /= [ | n IH].
by rewrite scal_one.
rewrite -scal_assoc.
Admitted.

Lemma ex_pseries_scal (c : K) (a : nat -> V) (x : K) : mult x c = mult c x -> ex_pseries a x -> ex_pseries (PS_scal c a) x.
Proof.
move => Hx [l Ha].
exists (scal c l).
by apply is_pseries_scal.
