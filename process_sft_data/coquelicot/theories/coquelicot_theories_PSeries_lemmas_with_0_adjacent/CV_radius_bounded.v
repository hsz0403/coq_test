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
rewrite Hn ; by apply Rle_trans with (2 := Rmax_r _ _), Rle_refl.
