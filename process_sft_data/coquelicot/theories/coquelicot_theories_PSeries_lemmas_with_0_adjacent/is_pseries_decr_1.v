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
apply filterlim_const.
