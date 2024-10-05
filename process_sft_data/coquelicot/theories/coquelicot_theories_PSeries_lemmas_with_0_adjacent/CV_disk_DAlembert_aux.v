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
apply Rabs_no_R0 => //.
