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
by rewrite -IH mult_one_r.
