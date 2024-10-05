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

Lemma PSeries_scal_r (c : R) (a : nat -> R) (x : R) : PSeries (PS_scal_r c a) x = PSeries a x * c.
Proof.
rewrite -Series_scal_r.
apply Series_ext.
move => n /=.
rewrite /PS_scal_r ; ring.
