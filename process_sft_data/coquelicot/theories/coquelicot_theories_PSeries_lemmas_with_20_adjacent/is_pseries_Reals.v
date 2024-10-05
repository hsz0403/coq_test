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

Lemma ex_pseries_dec {V : NormedModule R_AbsRing} (a : nat -> R) (x : R) : {ex_pseries a x} + {~ ex_pseries a x}.
Proof.
Admitted.

Lemma is_pseries_R (a : nat -> R) (x l : R) : is_pseries a x l <-> is_series (fun n : nat => a n * x ^ n) l.
Proof.
Admitted.

Lemma ex_pseries_R (a : nat -> R) (x : R) : ex_pseries a x <-> ex_series (fun n : nat => a n * x ^ n).
Proof.
Admitted.

Lemma PSeries_eq (a : nat -> R) (x : R) : PSeries a x = Series (fun k => scal (pow_n x k) (a k)).
Proof.
apply Series_ext.
intros n.
Admitted.

Lemma PSeries_1 (a : nat -> R) : PSeries a 1 = Series a.
Proof.
apply Series_ext => n.
Admitted.

Lemma ex_pseries_1 (a : nat -> R) : ex_pseries a 1 <-> ex_series a.
Proof.
assert (forall n : nat, scal (pow_n 1 n) (a n) = a n).
now intros n ; rewrite pow_n_pow pow1 scal_one.
Admitted.

Lemma is_pseries_unique (a : nat -> R) (x l : R) : is_pseries a x l -> PSeries a x = l.
Proof.
move => Ha; rewrite PSeries_eq.
Admitted.

Lemma PSeries_correct (a : nat -> R) (x : R) : ex_pseries a x -> is_pseries a x (PSeries a x).
Proof.
move => Ha; rewrite PSeries_eq.
apply Series_correct.
Admitted.

Lemma is_pseries_ext (a b : nat -> V) (x : K) (l:V) : (forall n, a n = b n) -> (is_pseries a x l) -> is_pseries b x l.
Proof.
move => Heq Ha.
apply is_series_ext with (2 := Ha).
move => n.
Admitted.

Lemma ex_pseries_ext (a b : nat -> V) (x : K) : (forall n, a n = b n) -> ex_pseries a x -> ex_pseries b x.
Proof.
move => Heq [l Ha].
Admitted.

Lemma PSeries_ext (a b : nat -> R) (x : R) : (forall n, a n = b n) -> PSeries a x = PSeries b x.
Proof.
move => Heq.
apply Series_ext.
Admitted.

Lemma is_pseries_0 (a : nat -> V) : is_pseries a zero (a O).
Proof.
apply filterlim_ext with (fun _ => a O).
elim => [ | n IH] /=.
now rewrite sum_O scal_one.
rewrite sum_Sn -IH /=.
rewrite mult_zero_l.
now rewrite scal_zero_l plus_zero_r.
Admitted.

Lemma ex_pseries_0 (a : nat -> V) : ex_pseries a zero.
Proof.
Admitted.

Lemma PSeries_0 (a : nat -> R) : PSeries a 0 = a O.
Proof.
rewrite PSeries_eq.
apply is_series_unique.
Admitted.

Lemma CV_disk_le (a : nat -> R) (r1 r2 : R) : Rabs r1 <= Rabs r2 -> CV_disk a r2 -> CV_disk a r1.
Proof.
move => H.
apply @ex_series_le => n.
rewrite /norm /= /abs /= Rabs_Rabsolu.
rewrite ?Rabs_mult ; apply Rmult_le_compat_l.
by apply Rabs_pos.
rewrite -?RPow_abs ; apply pow_incr ; split.
by apply Rabs_pos.
Admitted.

Lemma CV_disk_correct (a : nat -> R) (x : R) : CV_disk a x -> ex_pseries a x.
Proof.
intros H; apply ex_series_Rabs.
apply ex_series_ext with (2:=H).
intros n; apply f_equal.
Admitted.

Lemma CV_disk_0 (a : nat -> R) : CV_disk a 0.
Proof.
exists (Rabs (a O)).
apply (is_lim_seq_ext (fun _ => Rabs (a O)) _ (Rabs (a O))).
elim => /= [ | n IH].
by rewrite sum_O Rmult_1_r.
by rewrite sum_Sn /= Rmult_0_l Rmult_0_r Rabs_R0 /plus /= Rplus_0_r.
Admitted.

Lemma CV_radius_ge_0 (a : nat -> R) : Rbar_le (Finite 0) (CV_radius a).
Proof.
rewrite /CV_radius /Lub_Rbar ; case: ex_lub_Rbar => /= l Hl.
Admitted.

Lemma CV_radius_bounded (a : nat -> R) : is_lub_Rbar (fun r => exists M, forall n, Rabs (a n * r ^ n) <= M) (CV_radius a).
Proof.
rewrite /CV_radius /Lub_Rbar ; case: ex_lub_Rbar => cv /= [ub lub].
split.
move => r /= [M Hr].
have : forall y, Rabs y < Rabs r -> (CV_disk a) y.
move => y Hy ; rewrite /CV_disk /=.
set l := (Rabs (y / r)).
assert (ex_series (fun n => M * l ^ n)).
apply ex_series_ext with (fun n : nat => scal M (l ^ n)).
by elim.
apply: ex_series_scal_l.
apply ex_series_geom.
rewrite /l Rabs_Rabsolu Rabs_div.
apply Rlt_div_l.
apply Rle_lt_trans with (2 := Hy), Rabs_pos.
by rewrite Rmult_1_l.
have H : (Rabs r <> 0).
apply Rgt_not_eq, Rle_lt_trans with (2 := Hy), Rabs_pos.
contradict H.
by rewrite H Rabs_R0.
apply @ex_series_le with (2:=H) => n.
rewrite /norm /= /abs /= Rabs_Rabsolu.
replace (Rabs (a n * y ^ n)) with (Rabs (a n * r ^ n) * l^n).
apply Rmult_le_compat_r.
apply pow_le ; by apply Rabs_pos.
by apply Hr.
rewrite ?Rabs_mult Rmult_assoc ; apply Rmult_eq_compat_l.
rewrite /l RPow_abs -Rabs_mult.
apply f_equal.
elim: n => /= [ | n IH].
ring.
rewrite -IH ; field.
have Hr0 : Rabs r <> 0.
apply Rgt_not_eq, Rle_lt_trans with (2 := Hy), Rabs_pos.
contradict Hr0 ; by rewrite Hr0 Rabs_R0.
move => H.
have : forall y, Rabs y < Rabs r -> Rbar_le (Finite (y)) cv.
move => y Hy.
apply ub.
by apply (H y Hy).
have Hc0 : Rbar_le (Finite 0) cv.
apply ub, CV_disk_0.
case: (cv) Hc0 => [c | | ] // Hc0 Hcv.
case: (Rle_lt_dec r 0) => Hr0.
by apply Rle_trans with (1 := Hr0).
have H0 : forall e, 0 < e <= r -> r - e <= c.
intros.
apply Hcv.
apply Rlt_le_trans with (2 := Rle_abs _).
rewrite Rabs_pos_eq ; lra.
apply Rnot_lt_le => H1.
have H2: (c < ((c+r)/2) < r).
lra.
have H3 : 0 < ((r-c)/2) <= r.
unfold Rbar_le in Hc0 ; lra.
move: (H0 _ H3).
lra.
move => b Hb.
apply lub => x Hx.
apply Hb.
apply ex_series_lim_0 in Hx.
apply is_lim_seq_spec in Hx.
case: (Hx (mkposreal _ Rlt_0_1)) => /= {Hx} N Hx.
set M := fix f N := match N with | O => Rabs (a O * x ^ O) | S n => Rmax (f n) (Rabs (a (n) * x ^ (n))) end.
exists (Rmax (M N) 1) => n.
case: (le_lt_dec N n) => Hn.
apply Rle_trans with (2 := Rmax_r _ _).
move: (Hx n Hn).
rewrite Rminus_0_r Rabs_Rabsolu.
by apply Rlt_le.
apply Rle_trans with (2 := Rmax_l _ _).
elim: N n Hn {Hx} => [ | N IH] /= n Hn.
by apply lt_n_O in Hn.
apply lt_n_Sm_le, le_lt_eq_dec in Hn ; case: Hn => Hn.
apply Rle_trans with (2 := Rmax_l _ _).
by apply IH.
Admitted.

Lemma CV_disk_inside (a : nat -> R) (x : R) : Rbar_lt (Finite (Rabs x)) (CV_radius a) -> ex_series (fun n => Rabs (a n * x ^ n)).
Proof.
move => Ha.
assert (H : ~ ~ ex_series (fun n => Rabs (a n * x ^ n))).
contradict Ha.
apply Rbar_le_not_lt.
rewrite /CV_radius /Lub_Rbar ; case: ex_lub_Rbar => l /= [ub lub].
apply: lub => r Hr.
apply Rnot_lt_le ; contradict Ha.
move: Hr.
apply CV_disk_le.
by apply Rlt_le, Rlt_le_trans with (2 := Rle_abs _).
Admitted.

Lemma CV_radius_inside (a : nat -> R) (x : R) : Rbar_lt (Finite (Rabs x)) (CV_radius a) -> ex_pseries a x.
Proof.
move => Ha.
Admitted.

Lemma CV_disk_outside (a : nat -> R) (x : R) : Rbar_lt (CV_radius a) (Finite (Rabs x)) -> ~ is_lim_seq (fun n => a n * x ^ n) 0.
Proof.
case: (CV_radius_bounded a) => ub lub.
move => Hx.
have H : ~ (fun r : R => exists M : R, forall n : nat, Rabs (a n * r ^ n) <= M) x.
contradict Hx ; apply Rbar_le_not_lt.
apply ub.
case: Hx => M Hx.
exists M => n.
by rewrite Rabs_mult RPow_abs Rabs_Rabsolu -Rabs_mult.
contradict H.
apply is_lim_seq_spec in H.
case: (H (mkposreal _ Rlt_0_1)) => /= {Hx} N Hx.
set M := fix f N := match N with | O => Rabs (a O * x ^ O) | S n => Rmax (f n) (Rabs (a (n) * x ^ (n))) end.
exists (Rmax (M N) 1) => n.
case: (le_lt_dec N n) => Hn.
apply Rle_trans with (2 := Rmax_r _ _).
move: (Hx n Hn).
rewrite Rminus_0_r.
by apply Rlt_le.
apply Rle_trans with (2 := Rmax_l _ _).
elim: N n Hn {Hx} => [ | N IH] /= n Hn.
by apply lt_n_O in Hn.
apply lt_n_Sm_le, le_lt_eq_dec in Hn ; case: Hn => Hn.
apply Rle_trans with (2 := Rmax_l _ _).
by apply IH.
Admitted.

Lemma CV_radius_ext (a b : nat -> R) : (forall n, a n = b n) -> CV_radius a = CV_radius b.
Proof.
move => Heq.
rewrite /CV_radius /Lub_Rbar.
case: ex_lub_Rbar => la [ub_a lub_a] ; case: ex_lub_Rbar => lb [ub_b lub_b] /=.
apply Rbar_le_antisym.
apply lub_a => x Hx.
apply ub_b ; move: Hx.
apply ex_series_ext => n ; by rewrite Heq.
apply lub_b => x Hx.
apply ub_a ; move: Hx.
Admitted.

Lemma CV_disk_DAlembert_aux (a : nat -> R) (x k : R) : x <> 0 -> (forall n, a n <> 0) -> (is_lim_seq (fun n => Rabs (a (S n) / a n)) k <-> is_lim_seq (fun n => Rabs ((a (S n) * x^(S n)) / (a n * x ^ n))) (Rabs x * k)).
Proof.
move => Hx Ha ; split => H.
evar (l : Rbar).
replace (Finite (Rabs x * k)) with l.
apply is_lim_seq_ext with (fun n => Rabs x * Rabs (a (S n) / a n)).
move => n ; rewrite ?Rabs_div => //=.
rewrite ?Rabs_mult.
field.
split ; apply Rabs_no_R0 => //.
by apply pow_nonzero.
apply Rmult_integral_contrapositive_currified => //.
by apply pow_nonzero.
apply is_lim_seq_scal_l.
apply H.
by simpl.
evar (l : Rbar).
replace (Finite k) with l.
apply is_lim_seq_ext with (fun n : nat => /Rabs x * Rabs (a (S n) * x ^ S n / (a n * x ^ n))).
move => n ; rewrite /= ?Rabs_div ?Rabs_mult.
field.
repeat split ; apply Rabs_no_R0 => //.
by apply pow_nonzero.
by apply Ha.
apply Rmult_integral_contrapositive_currified => //.
by apply pow_nonzero.
apply is_lim_seq_scal_l.
apply H.
apply Rbar_finite_eq ; field.
Admitted.

Lemma CV_disk_DAlembert (a : nat -> R) (x:R) l : (forall n:nat, a n <> 0) -> is_lim_seq (fun n:nat => Rabs (a (S n) / a n)) (Finite l) -> (l = 0 \/ (l <> 0 /\ Rabs x < / l)) -> CV_disk a x.
Proof.
move => Ha Hl H.
case: (Req_dec x 0) => Hx.
rewrite Hx.
exists (Rabs (a O)).
apply (is_lim_seq_ext (fun _ => Rabs (a O)) _ (Rabs (a 0%nat))).
elim => /= [ | n IH].
by rewrite sum_O Rmult_1_r.
by rewrite sum_Sn /= Rmult_0_l Rmult_0_r Rabs_R0 /plus /= Rplus_0_r.
apply is_lim_seq_const.
apply ex_series_DAlembert with (Rabs x * l).
case: H => H.
rewrite H Rmult_0_r ; by apply Rlt_0_1.
replace 1 with (/ l * l) by (field ; apply H).
apply Rmult_lt_compat_r.
apply Rnot_le_lt ; case => H0.
case: H => H.
apply Rle_not_lt.
apply Rlt_le, Rlt_le_trans with 0.
by apply Rinv_lt_0_compat.
by apply Rabs_pos.
by case: H.
by apply H.
move => n ; apply Rmult_integral_contrapositive_currified.
by apply Ha.
by apply pow_nonzero.
Admitted.

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

Lemma is_pseries_Reals (a : nat -> R) (x l : R) : is_pseries a x l <-> Pser a x l.
Proof.
split => H.
move => e He ; set eps := mkposreal e He.
apply (is_lim_seq_spec _ l) in H.
case: (H eps) => {H} N H.
exists N => n Hn.
rewrite <- sum_n_Reals.
rewrite (sum_n_ext _ (fun n0 : nat => scal (pow_n x n0) (a n0))).
by apply H.
intros k; rewrite pow_n_pow /=; apply Rmult_comm.
apply (is_lim_seq_spec _ l).
move => eps.
case: (H eps (cond_pos eps)) => {H} N H.
exists N => n Hn.
rewrite (sum_n_ext _ (fun n0 : nat => a n0 * x ^ n0)).
rewrite sum_n_Reals.
by apply H.
intros; now rewrite Rmult_comm pow_n_pow.
