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

Lemma PSeries_continuity (a : nat -> R) (x : R) : Rbar_lt (Finite (Rabs x)) (CV_radius a) -> continuity_pt (PSeries a) x.
Proof.
move => H.
case: (CV_radius_Reals_2 a x H) => r H0.
apply (CVU_continuity (fun (n : nat) (x : R) => sum_f_R0 (fun k : nat => a k * x ^ k) n) (PSeries a) x r H0).
move => n y Hy.
apply continuity_pt_finite_SF.
move => k Hk.
apply continuity_pt_scal.
elim: k {Hk} => /= [ | k IH].
by apply continuity_pt_const => d f.
apply continuity_pt_mult.
apply derivable_continuous_pt, derivable_pt_id.
by apply IH.
Admitted.

Lemma CV_radius_derive (a : nat -> R) : CV_radius (PS_derive a) = CV_radius a.
Admitted.

Lemma is_derive_PSeries (a : nat -> R) (x : R) : Rbar_lt (Finite (Rabs x)) (CV_radius a) -> is_derive (PSeries a) x (PSeries (PS_derive a) x).
Proof.
move => Hx.
case: (CV_radius_Reals_2 _ _ Hx) => r0 Hr0 ; rewrite -CV_radius_derive in Hx ; case: (CV_radius_Reals_2 _ _ Hx) => r1 Hr1 ; rewrite CV_radius_derive in Hx.
apply CVU_dom_Reals in Hr0 ; apply CVU_dom_Reals in Hr1.
have Hr : 0 < (Rmin r0 r1).
apply Rmin_case.
by apply r0.
by apply r1.
set D := (Boule x (mkposreal _ Hr)).
assert (Ho : open D).
move => y Hy.
apply Rabs_lt_between' in Hy ; simpl in Hy.
have H : 0 < Rmin ((x+Rmin r0 r1)-y) (y-(x-Rmin r0 r1)).
apply Rmin_case.
rewrite -(Rminus_eq_0 y) ; by apply Rplus_lt_compat_r, Hy.
rewrite -(Rminus_eq_0 ((x-Rmin r0 r1))) /Rminus ; by apply Rplus_lt_compat_r , Hy.
exists (mkposreal _ H) => /= z Hz.
apply Rabs_lt_between' ; split ; apply (Rplus_lt_reg_l (-y)) ; simpl.
apply Ropp_lt_cancel.
apply Rle_lt_trans with (1 := Rabs_maj2 _).
rewrite Ropp_plus_distr ?Ropp_involutive (Rplus_comm (-y)).
apply Rlt_le_trans with (1 := Hz).
exact: Rmin_r.
apply Rle_lt_trans with (1 := Rle_abs _).
rewrite ?(Rplus_comm (-y)).
apply Rlt_le_trans with (1 := Hz).
exact: Rmin_l.
have Hc : is_connected D.
move => x0 y z Hx0 Hy Hx0yz.
rewrite /D.
case: Hx0yz => H1 H2.
apply (Rplus_le_compat_r (-x)) in H1.
apply (Rplus_le_compat_r (-x)) in H2.
move: (conj H1 H2) => {H1 H2} Hxyz.
apply Rabs_le_between_Rmax in Hxyz.
apply Rle_lt_trans with (1 := Hxyz) => /=.
apply Rmax_case.
apply Rle_lt_trans with (1 := Rle_abs _).
exact: Hy.
apply Rle_lt_trans with (1 := Rabs_maj2 _).
exact: Hx0.
have Hfn : CVU_dom (fun (n : nat) (y : R) => sum_f_R0 (fun k : nat => a k * y ^ k) n) D.
apply CVU_dom_include with (Boule x r0).
move => y Hy.
by apply Rlt_le_trans with (1 := Hy), Rmin_l.
exact: Hr0.
have Idn : (forall (n : nat) (x : R), (0 < n)%nat -> is_derive (fun (y : R) => sum_f_R0 (fun k : nat => a k * y ^ k) n) x (sum_f_R0 (fun k : nat => (PS_derive a) k * x ^ k) (pred n))).
case => [ y Hn | n y _ ].
by apply lt_irrefl in Hn.
elim: n => [ | n] ; simpl pred ; rewrite /sum_f_R0 -/sum_f_R0.
replace (PS_derive a 0 * y ^ 0) with (0 + a 1%nat * (1 * 1)) by (rewrite /PS_derive /= ; ring).
apply: is_derive_plus.
simpl.
apply: is_derive_const.
apply is_derive_scal.
apply: is_derive_scal_l.
apply: is_derive_id.
move => IH.
apply: is_derive_plus.
apply IH.
rewrite /PS_derive.
replace (INR (S (S n)) * a (S (S n)) * y ^ S n) with (a (S (S n)) * (INR (S (S n)) * y^S n)) by ring.
by apply is_derive_Reals, derivable_pt_lim_scal, derivable_pt_lim_pow.
have Edn : (forall (n : nat) (x : R), D x -> ex_derive (fun (y : R) => sum_f_R0 (fun k : nat => a k * y ^ k) n) x).
case => [ | n] y Hy.
simpl.
apply: ex_derive_const.
exists (sum_f_R0 (fun k : nat => PS_derive a k * y ^ k) (pred (S n))).
apply (Idn (S n) y).
by apply lt_O_Sn.
have Cdn : (forall (n : nat) (x : R), D x -> continuity_pt (Derive ((fun (n0 : nat) (y : R) => sum_f_R0 (fun k : nat => a k * y ^ k) n0) n)) x).
have Cdn : (forall (n : nat) (x : R), D x -> continuity_pt (fun x => sum_f_R0 (fun k : nat => PS_derive a k * x ^ k) n) x).
move => n y Hy.
apply derivable_continuous_pt.
elim: n => [ /= | n IH].
exact: derivable_pt_const.
apply derivable_pt_plus ; rewrite -/sum_f_R0.
exact: IH.
apply derivable_pt_scal, derivable_pt_pow.
case => [ | n] y Hy.
simpl ; by apply continuity_pt_const => z.
move => e He ; case: (Cdn n y Hy e He) => {Cdn} d [Hd Cdn].
destruct (Ho y Hy) as [d0 Hd0].
have Hd1 : 0 < Rmin d d0.
apply Rmin_case ; [exact: Hd | by apply d0].
exists (mkposreal _ Hd1) ; split.
exact: Hd1.
move => z Hz ; simpl in Hz.
rewrite (is_derive_unique _ _ _ (Idn (S n) z (lt_O_Sn _))).
rewrite (is_derive_unique _ _ _ (Idn (S n) y (lt_O_Sn _))).
apply (Cdn z) ; split.
by apply Hz.
apply Rlt_le_trans with (1 := proj2 Hz), Rmin_l.
have Hdn : CVU_dom (fun (n : nat) (x : R) => Derive ((fun (n0 : nat) (y : R) => sum_f_R0 (fun k : nat => a k * y ^ k) n0) n) x) D.
apply CVU_dom_include with (Boule x r1).
move => y Hy.
by apply Rlt_le_trans with (1 := Hy), Rmin_r.
apply CVU_dom_cauchy ; apply CVU_dom_cauchy in Hr1.
move => eps.
case: (Hr1 eps) => {Hr1} N Hr1.
exists (S N) => n m y Hy Hn Hm.
case: n Hn => [ | n] Hn.
by apply le_Sn_O in Hn.
apply le_S_n in Hn.
case: m Hm => [ | m] Hm.
by apply le_Sn_O in Hm.
apply le_S_n in Hm.
rewrite (is_derive_unique _ _ _ (Idn (S n) y (lt_O_Sn _))).
rewrite (is_derive_unique _ _ _ (Idn (S m) y (lt_O_Sn _))).
by apply Hr1.
have Hx' : D x.
by rewrite /D /Boule /= Rminus_eq_0 Rabs_R0.
have H := (CVU_Derive (fun n y => (sum_f_R0 (fun k : nat => a k * y ^ k)) n) D Ho Hc Hfn Edn Cdn Hdn x Hx').
replace (PSeries (PS_derive a) x) with (real (Lim_seq (fun n : nat => Derive (fun y : R => sum_f_R0 (fun k : nat => a k * y ^ k) n) x))).
apply: is_derive_ext H.
simpl => t.
apply (f_equal real), Lim_seq_ext.
intros n; apply sym_eq, sum_n_Reals.
rewrite -Lim_seq_incr_1.
apply (f_equal real), Lim_seq_ext => n.
rewrite sum_n_Reals.
apply is_derive_unique, Idn.
by apply lt_O_Sn.
move => y Hy.
apply sym_eq.
apply is_lim_seq_unique.
apply is_lim_seq_spec.
move => eps.
case: (Hr1 eps (cond_pos eps)) => {Hr1} N Hr1.
exists N => n Hn.
rewrite -Rabs_Ropp Ropp_minus_distr'.
by apply Hr1.
move => y Hy.
apply sym_eq.
apply is_lim_seq_unique.
apply is_lim_seq_spec.
move => eps.
case: (Hr0 eps (cond_pos eps)) => {Hr0} N Hr0.
exists N => n Hn.
rewrite -Rabs_Ropp Ropp_minus_distr'.
by apply Hr0.
move => y Hy.
apply sym_eq.
apply is_lim_seq_unique.
apply is_lim_seq_spec.
move => eps.
case: (Hr1 eps (cond_pos eps)) => {Hr1} N Hr1.
exists N => n Hn.
rewrite -Rabs_Ropp Ropp_minus_distr'.
Admitted.

Lemma ex_derive_PSeries (a : nat -> R) (x : R) : Rbar_lt (Finite (Rabs x)) (CV_radius a) -> ex_derive (PSeries a) x.
Proof.
move => Hx ; exists (PSeries (PS_derive a) x).
Admitted.

Lemma Derive_PSeries (a : nat -> R) (x : R) : Rbar_lt (Finite (Rabs x)) (CV_radius a) -> Derive (PSeries a) x = PSeries (PS_derive a) x.
Proof.
move => H.
apply is_derive_unique.
Admitted.

Lemma is_pseries_derive (a : nat -> R) x : Rbar_lt (Rabs x) (CV_radius a) -> is_pseries (PS_derive a) x (Derive (PSeries a) x).
Proof.
intros Hx.
assert (Ha := is_derive_PSeries _ _ Hx).
apply is_derive_unique in Ha.
rewrite Ha.
apply PSeries_correct.
Admitted.

Lemma ex_pseries_derive (a : nat -> R) (x : R) : Rbar_lt (Finite (Rabs x)) (CV_radius a) -> ex_pseries (PS_derive a) x.
Proof.
move => Hx.
eexists.
Admitted.

Lemma is_derive_n_PSeries (n : nat) (a : nat -> R) : forall x, Rbar_lt (Rabs x) (CV_radius a) -> is_derive_n (PSeries a) n x (PSeries (PS_derive_n n a) x).
Proof.
elim: n => [ | n IH] x Hx.
simpl ; rewrite /PS_derive_n /=.
apply PSeries_ext => n.
rewrite -plus_n_O.
field.
apply Rgt_not_eq.
by apply INR_fact_lt_0.
simpl ; rewrite /PS_derive_n /=.
apply is_derive_ext_loc with (PSeries (fun k : nat => INR (fact (k + n)) / INR (fact k) * a (k + n)%nat)).
case Ha : (CV_radius a) => [cva | | ].
move: (Hx) ; rewrite Ha ; move/Rminus_lt_0 => Hx0.
exists (mkposreal _ Hx0) => /= y Hy.
apply sym_eq.
apply is_derive_n_unique.
apply IH.
rewrite Ha /=.
replace y with ((y-x) + x) by ring.
apply Rle_lt_trans with (1 := Rabs_triang _ _).
by apply Rlt_minus_r.
exists (mkposreal _ Rlt_0_1) => /= y Hy.
apply sym_eq.
apply is_derive_n_unique.
apply IH.
by rewrite Ha /=.
by rewrite Ha in Hx.
evar (l : R).
replace (PSeries _ x) with l.
rewrite /l {l}.
apply is_derive_PSeries.
replace (CV_radius (fun k : nat => INR (fact (k + n)) / INR (fact k) * a (k + n)%nat)) with (CV_radius a).
by apply Hx.
elim: n {IH} => [ | n IH].
apply CV_radius_ext => n.
rewrite -plus_n_O.
field.
apply Rgt_not_eq.
by apply INR_fact_lt_0.
rewrite IH.
rewrite -CV_radius_derive.
apply CV_radius_ext => k.
rewrite /PS_derive.
rewrite -plus_n_Sm plus_Sn_m /fact -/fact ?mult_INR ?S_INR.
field.
rewrite -S_INR ; split ; apply Rgt_not_eq.
by apply INR_fact_lt_0.
apply (lt_INR O), lt_O_Sn.
rewrite /l {l}.
apply PSeries_ext.
move => k ; rewrite /PS_derive.
rewrite -plus_n_Sm plus_Sn_m /fact -/fact ?mult_INR ?S_INR.
field.
rewrite -S_INR ; split ; apply Rgt_not_eq.
by apply INR_fact_lt_0.
Admitted.

Lemma ex_derive_n_PSeries (n : nat) (a : nat -> R) (x : R) : Rbar_lt (Finite (Rabs x)) (CV_radius a) -> ex_derive_n (PSeries a) n x.
Proof.
elim: n a x => [ | n IH] a x Hx.
by simpl.
simpl.
exists (PSeries (PS_derive_n (S n) a) x).
Admitted.

Lemma Derive_n_PSeries (n : nat) (a : nat -> R) (x : R) : Rbar_lt (Finite (Rabs x)) (CV_radius a) -> Derive_n (PSeries a) n x = PSeries (PS_derive_n n a) x.
Proof.
move => H.
apply is_derive_n_unique.
Admitted.

Lemma CV_radius_derive_n (n : nat) (a : nat -> R) : CV_radius (PS_derive_n n a) = CV_radius a.
Proof.
elim: n a => [ | n IH] /= a.
apply CV_radius_ext.
move => k ; rewrite /PS_derive_n /=.
rewrite plus_0_r ; field.
by apply INR_fact_neq_0.
rewrite -(CV_radius_derive a).
rewrite -(IH (PS_derive a)).
apply CV_radius_ext.
move => k ; rewrite /PS_derive_n /PS_derive.
rewrite -plus_n_Sm /fact -/fact mult_INR ; field.
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
rewrite sum_Sn /= /plus /= IH ; ring.
