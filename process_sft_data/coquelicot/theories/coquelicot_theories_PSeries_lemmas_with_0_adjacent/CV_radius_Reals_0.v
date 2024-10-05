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
by apply Rlt_le, r.
