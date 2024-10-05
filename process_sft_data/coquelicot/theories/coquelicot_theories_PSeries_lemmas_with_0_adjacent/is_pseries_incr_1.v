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
now apply filterlim_comp with (2 := filterlim_scal_r _ _).
