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
lra.
