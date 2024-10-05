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

Lemma Derive_n_coef (a : nat -> R) (n : nat) : Rbar_lt (Finite 0) (CV_radius a) -> Derive_n (PSeries a) n 0 = a n * (INR (fact n)).
Proof.
elim: n a => [ | n IH] a Ha.
rewrite Rmult_1_r.
rewrite /= /PSeries /Series -(Lim_seq_ext (fun _ => a O)).
by rewrite Lim_seq_const.
elim => /= [ | n IH].
rewrite sum_O ; ring.
rewrite sum_Sn -IH /plus /= ; ring.
simpl Derive_n.
replace (Derive (Derive_n (PSeries a) n) 0) with (Derive_n (PSeries (PS_derive a)) n 0).
rewrite IH.
rewrite /fact -/fact mult_INR /PS_derive ; ring.
by rewrite CV_radius_derive.
transitivity (Derive_n (Derive (PSeries a)) n 0).
apply Derive_n_ext_loc.
case: (Rbar_eq_dec (CV_radius a) p_infty) => H.
exists (mkposreal _ Rlt_0_1) => /= x Hx.
apply sym_eq ; apply Derive_PSeries.
by rewrite H.
have Hc : 0 < real (CV_radius a).
case: (CV_radius a) Ha H => /= [c | | ] Ha H ; by [].
exists (mkposreal _ Hc) => /= x Hx.
apply sym_eq ; apply Derive_PSeries.
case: (CV_radius a) Hx Ha => /= [c | | ] Hx Ha //.
by rewrite /ball /= /AbsRing_ball /= /minus /plus /opp /= -/(Rminus _ _) Rminus_0_r in Hx.
move: (Derive_n_comp (PSeries a) n 1%nat 0) => /= ->.
by replace (n+1)%nat with (S n) by ring.
