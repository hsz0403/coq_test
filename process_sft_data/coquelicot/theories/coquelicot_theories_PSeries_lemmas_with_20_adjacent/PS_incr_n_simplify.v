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

Lemma CV_radius_finite_DAlembert (a : nat -> R) (l : R) : (forall n:nat, a n <> 0) -> 0 < l -> is_lim_seq (fun n:nat => Rabs (a (S n) / a n)) l -> CV_radius a = Finite (/l).
Proof.
move => Ha Hl Hda.
apply Rbar_le_antisym.
rewrite /CV_radius /Lub_Rbar ; case: ex_lub_Rbar => /= cv [ub lub].
apply lub => x Hax.
case: (Rle_lt_dec x 0) => Hx.
apply Rlt_le, Rle_lt_trans with 0.
by apply Hx.
by apply Rinv_0_lt_compat.
rewrite -(Rabs_pos_eq x (Rlt_le _ _ Hx)).
rewrite -(Rmult_1_l (/l)).
replace (Rabs x) with ((Rabs x * l) /l) by (field ; apply Rgt_not_eq, Hl).
apply Rmult_le_compat_r.
by apply Rlt_le, Rinv_0_lt_compat.
apply Rnot_lt_le.
contradict Hax.
have : CV_disk a x -> is_lim_seq (fun n => a n * x ^ n) 0.
move => H.
apply ex_series_lim_0.
by apply ex_series_Rabs.
move => H H0.
move: (H H0) => {H H0}.
apply not_ex_series_DAlembert with (Rabs x * l) => //.
move => n.
apply Rmult_integral_contrapositive_currified => //.
by apply pow_nonzero, Rgt_not_eq.
apply CV_disk_DAlembert_aux.
by apply Rgt_not_eq.
by apply Ha.
by apply Hda.
apply Rbar_not_lt_le.
move : (CV_disk_outside a).
rewrite /CV_radius /Lub_Rbar ; case: ex_lub_Rbar ; case => [cv | | ] /= [ub lub] Hnot_ex H ; try by auto.
suff H0 : cv < ((cv+/l)/2) < /l.
absurd (ex_series (fun n => Rabs (a n * ((cv+/l)/2)^n))).
suff H1 : cv < Rabs ((cv + / l) / 2).
move: (Hnot_ex ((cv + / l) / 2) H1) => {Hnot_ex} Hnot_ex.
contradict Hnot_ex ; by apply ex_series_lim_0, ex_series_Rabs.
apply Rlt_le_trans with (2 := Rle_abs _), H0.
apply (CV_disk_DAlembert) with l.
by apply Ha.
by apply Hda.
right ; split.
by apply Rgt_not_eq.
rewrite Rabs_pos_eq.
by apply H0.
apply Rlt_le, Rle_lt_trans with (2 := proj1 H0).
apply ub.
exists (Rabs (a O)).
apply (is_lim_seq_ext (fun _ => Rabs (a O)) _ (Rabs (a 0%nat))).
elim => [ | n IH] /=.
by rewrite sum_O Rmult_1_r.
by rewrite sum_Sn /= Rmult_0_l Rmult_0_r Rabs_R0 /plus /= Rplus_0_r.
by apply is_lim_seq_const.
lra.
case: (ub 0) => //.
exists (Rabs (a O)).
apply (is_lim_seq_ext (fun _ => Rabs (a O)) _ (Rabs (a 0%nat))).
elim => [ | n IH] /=.
by rewrite sum_O Rmult_1_r.
by rewrite sum_Sn /= Rmult_0_l Rmult_0_r Rabs_R0 /plus /= Rplus_0_r.
Admitted.

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

Lemma ex_pseries_scal (c : K) (a : nat -> V) (x : K) : mult x c = mult c x -> ex_pseries a x -> ex_pseries (PS_scal c a) x.
Proof.
move => Hx [l Ha].
exists (scal c l).
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

Lemma is_pseries_incr_n (a : nat -> V) (n : nat) (x : K) (l : V) : is_pseries a x l -> is_pseries (PS_incr_n a n) x (scal (pow_n x n) l).
Proof.
move => Ha.
elim: n => /= [ | n IH].
by rewrite scal_one.
rewrite -scal_assoc.
Admitted.

Lemma ex_pseries_incr_n (a : nat -> V) (n : nat) (x : K) : ex_pseries a x -> ex_pseries (PS_incr_n a n) x.
Proof.
move => [l Ha].
Admitted.

Lemma is_pseries_decr_1 (a : nat -> V) (x y : K) (l : V) : mult y x = one -> is_pseries a x l -> is_pseries (PS_decr_1 a) x (scal y (plus l (opp (a O)))).
Proof.
move => Hx Ha.
apply filterlim_ext with (fun n : nat => scal y (sum_n (fun k => scal (pow_n x (S k)) (a (S k))) n)).
intros n; induction n; unfold PS_decr_1; simpl.
rewrite !sum_O mult_one_r scal_one scal_assoc.
rewrite Hx; try assumption.
apply @scal_one.
rewrite !sum_Sn -IHn.
rewrite scal_distr_l; apply f_equal.
rewrite scal_assoc (mult_assoc y).
rewrite Hx.
now rewrite mult_one_l.
apply filterlim_comp with (2 := filterlim_scal_r _ _).
apply filterlim_ext with (fun n : nat => plus (sum_n (fun k => scal (pow_n x k) (a k)) (S n)) (opp (a 0%nat))).
intros n; induction n; simpl.
rewrite sum_Sn !sum_O /= mult_one_r scal_one.
rewrite plus_comm plus_assoc.
now rewrite plus_opp_l plus_zero_l.
rewrite !sum_Sn -IHn.
apply sym_eq; rewrite plus_comm plus_assoc.
apply f_equal2;[idtac|reflexivity].
now rewrite !sum_Sn plus_comm.
apply filterlim_comp_2 with (3 := filterlim_plus _ _).
apply filterlim_comp with (f:= fun x => S x) (2:=Ha).
apply eventually_subseq; intros n; omega.
Admitted.

Lemma ex_pseries_decr_1 (a : nat -> V) (x : K) : (x = zero \/ exists y, mult y x = one) -> ex_pseries a x -> ex_pseries (PS_decr_1 a) x.
Proof.
case => [H | [y Hx]] [l Ha].
rewrite H ; by apply ex_pseries_0.
exists (scal y (plus l (opp (a 0%nat)))).
Admitted.

Lemma is_pseries_decr_n (a : nat -> V) (n : nat) (x y:K) (l : V) : mult y x = one -> (0 < n)%nat -> is_pseries a x l -> is_pseries (PS_decr_n a n) x (scal (pow_n y n) (plus l (opp (sum_n (fun k => scal (pow_n x k) (a k)) (n-1)%nat)))).
Proof.
move => Hx Hn Ha.
case: n Hn => [ | n] Hn.
by apply lt_irrefl in Hn.
clear Hn ; simpl ; rewrite -minus_n_O /PS_decr_n /=.
elim: n => /= [ | n IH].
rewrite sum_O scal_one mult_one_r.
now apply is_pseries_decr_1.
set (ln := (scal (mult y (pow_n y n)) (plus l (opp (sum_n (fun k : nat => scal (pow_n x k) (a k)) n))))) in IH.
rewrite !sum_Sn /=.
replace (scal (mult y (mult y (pow_n y n))) (plus l (opp (plus (sum_n (fun k : nat => scal (pow_n x k) (a k)) n) (scal (mult x (pow_n x n)) (a (S n))))))) with (scal y (plus ln (opp (a (S (n + 0)))))).
assert (Y:is_pseries (fun k : nat => a (S (n + k))) x ln).
apply IH.
move: (is_pseries_decr_1 (fun k : nat => a (S (n + k))) x y ln Hx Y).
rewrite /PS_decr_1 /=.
apply is_pseries_ext => k.
apply f_equal ; ring.
rewrite -scal_assoc.
apply f_equal; unfold ln.
repeat rewrite (scal_distr_l _ l).
rewrite -plus_assoc; apply f_equal.
rewrite opp_plus scal_distr_l; apply f_equal.
rewrite plus_0_r -scal_opp_l scal_assoc.
apply trans_eq with (scal (opp (one : K)) (a (S n))).
now rewrite scal_opp_l scal_one.
apply f_equal2; try reflexivity.
rewrite <- opp_mult_r; apply f_equal.
clear -Hx.
rewrite -?/(pow_n _ (S _)).
elim: (S n) => {n} /= [ | n IH].
by rewrite mult_one_l.
rewrite -(pow_n_comm_1 x) mult_assoc.
rewrite -(mult_assoc y (pow_n y n) (pow_n x n)).
Admitted.

Lemma ex_pseries_decr_n (a : nat -> V) (n : nat) (x : K) : (x = zero \/ exists y, mult y x = one) -> ex_pseries a x -> ex_pseries (PS_decr_n a n) x.
Proof.
intros Hx H.
induction n.
unfold PS_decr_n; now simpl.
apply ex_pseries_ext with ((PS_decr_1 (PS_decr_n a n))).
intros m; unfold PS_decr_1, PS_decr_n.
apply f_equal; ring.
apply ex_pseries_decr_1.
apply Hx.
Admitted.

Lemma PSeries_incr_1 a x : PSeries (PS_incr_1 a) x = x * PSeries a x.
Proof.
rewrite -Series_scal_l.
unfold PSeries, Series.
rewrite -(Lim_seq_incr_1 (sum_n (fun k : nat => PS_incr_1 a k * x ^ k))) /=.
apply f_equal, Lim_seq_ext.
case.
rewrite sum_Sn !sum_O /= /plus /zero /=.
ring.
elim => /= [ | n IH].
rewrite !sum_Sn !sum_O /= /plus /zero /=.
ring.
rewrite sum_Sn IH !sum_Sn /= /plus /=.
Admitted.

Lemma PSeries_incr_n (a : nat -> R) (n : nat) (x : R) : PSeries (PS_incr_n a n) x = x^n * PSeries a x.
Proof.
elim: n => /= [ | n IH].
by rewrite Rmult_1_l.
rewrite Rmult_assoc.
Admitted.

Lemma PSeries_decr_1 (a : nat -> R) (x : R) : ex_pseries a x -> PSeries a x = a O + x * PSeries (PS_decr_1 a) x.
Proof.
intros Ha.
case: (Req_dec x 0) => Hx.
rewrite Hx PSeries_0 ; ring.
move: (is_pseries_decr_1 a x (/x) (PSeries a x) (Rinv_l _ Hx) (PSeries_correct _ _ Ha)) => Hb.
rewrite (is_pseries_unique _ _ _ Hb).
rewrite /plus /opp /scal /= /mult /=.
Admitted.

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

Lemma PSeries_odd_even (a : nat -> R) (x : R) : ex_pseries (fun n => a (2*n)%nat) (x^2) -> ex_pseries (fun n => a (2*n+1)%nat) (x^2) -> PSeries a x = PSeries (fun n => a (2*n)%nat) (x^2) + x * PSeries (fun n => a (2*n+1)%nat) (x^2).
Proof.
move => H1 H2 ; apply is_pseries_unique.
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
by apply IH, lt_S_n.
