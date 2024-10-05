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

Lemma is_pseries_R (a : nat -> R) (x l : R) : is_pseries a x l <-> is_series (fun n : nat => a n * x ^ n) l.
Proof.
Admitted.

Lemma ex_pseries_R (a : nat -> R) (x : R) : ex_pseries a x <-> ex_series (fun n : nat => a n * x ^ n).
Proof.
Admitted.

Lemma PSeries_eq (a : nat -> R) (x : R) : PSeries a x = Series (fun k => scal (pow_n x k) (a k)).
Proof.
apply Series_ext.
intros n.
Admitted.

Lemma PSeries_1 (a : nat -> R) : PSeries a 1 = Series a.
Proof.
apply Series_ext => n.
Admitted.

Lemma ex_pseries_1 (a : nat -> R) : ex_pseries a 1 <-> ex_series a.
Proof.
assert (forall n : nat, scal (pow_n 1 n) (a n) = a n).
now intros n ; rewrite pow_n_pow pow1 scal_one.
Admitted.

Lemma is_pseries_unique (a : nat -> R) (x l : R) : is_pseries a x l -> PSeries a x = l.
Proof.
move => Ha; rewrite PSeries_eq.
Admitted.

Lemma PSeries_correct (a : nat -> R) (x : R) : ex_pseries a x -> is_pseries a x (PSeries a x).
Proof.
move => Ha; rewrite PSeries_eq.
apply Series_correct.
Admitted.

Lemma is_pseries_Reals (a : nat -> R) (x l : R) : is_pseries a x l <-> Pser a x l.
Proof.
split => H.
move => e He ; set eps := mkposreal e He.
apply (is_lim_seq_spec _ l) in H.
case: (H eps) => {H} N H.
exists N => n Hn.
rewrite <- sum_n_Reals.
rewrite (sum_n_ext _ (fun n0 : nat => scal (pow_n x n0) (a n0))).
by apply H.
intros k; rewrite pow_n_pow /=; apply Rmult_comm.
apply (is_lim_seq_spec _ l).
move => eps.
case: (H eps (cond_pos eps)) => {H} N H.
exists N => n Hn.
rewrite (sum_n_ext _ (fun n0 : nat => a n0 * x ^ n0)).
rewrite sum_n_Reals.
by apply H.
Admitted.

Lemma is_pseries_ext (a b : nat -> V) (x : K) (l:V) : (forall n, a n = b n) -> (is_pseries a x l) -> is_pseries b x l.
Proof.
move => Heq Ha.
apply is_series_ext with (2 := Ha).
move => n.
Admitted.

Lemma ex_pseries_ext (a b : nat -> V) (x : K) : (forall n, a n = b n) -> ex_pseries a x -> ex_pseries b x.
Proof.
move => Heq [l Ha].
Admitted.

Lemma ex_pseries_dec {V : NormedModule R_AbsRing} (a : nat -> R) (x : R) : {ex_pseries a x} + {~ ex_pseries a x}.
Proof.
apply ex_series_dec.
