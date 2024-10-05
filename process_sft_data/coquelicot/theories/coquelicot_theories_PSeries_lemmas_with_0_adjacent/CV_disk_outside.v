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
rewrite Hn ; by apply Rle_trans with (2 := Rmax_r _ _), Rle_refl.
