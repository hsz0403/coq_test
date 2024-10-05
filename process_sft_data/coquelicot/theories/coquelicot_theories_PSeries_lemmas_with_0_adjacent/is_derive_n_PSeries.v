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

Lemma is_derive_n_PSeries (n : nat) (a : nat -> R) : forall x, Rbar_lt (Rabs x) (CV_radius a) -> is_derive_n (PSeries a) n x (PSeries (PS_derive_n n a) x).
Proof.
elim: n => [ | n IH] x Hx.
simpl ; rewrite /PS_derive_n /=.
apply PSeries_ext => n.
rewrite -plus_n_O.
field.
apply Rgt_not_eq.
by apply INR_fact_lt_0.
simpl ; rewrite /PS_derive_n /=.
apply is_derive_ext_loc with (PSeries (fun k : nat => INR (fact (k + n)) / INR (fact k) * a (k + n)%nat)).
case Ha : (CV_radius a) => [cva | | ].
move: (Hx) ; rewrite Ha ; move/Rminus_lt_0 => Hx0.
exists (mkposreal _ Hx0) => /= y Hy.
apply sym_eq.
apply is_derive_n_unique.
apply IH.
rewrite Ha /=.
replace y with ((y-x) + x) by ring.
apply Rle_lt_trans with (1 := Rabs_triang _ _).
by apply Rlt_minus_r.
exists (mkposreal _ Rlt_0_1) => /= y Hy.
apply sym_eq.
apply is_derive_n_unique.
apply IH.
by rewrite Ha /=.
by rewrite Ha in Hx.
evar (l : R).
replace (PSeries _ x) with l.
rewrite /l {l}.
apply is_derive_PSeries.
replace (CV_radius (fun k : nat => INR (fact (k + n)) / INR (fact k) * a (k + n)%nat)) with (CV_radius a).
by apply Hx.
elim: n {IH} => [ | n IH].
apply CV_radius_ext => n.
rewrite -plus_n_O.
field.
apply Rgt_not_eq.
by apply INR_fact_lt_0.
rewrite IH.
rewrite -CV_radius_derive.
apply CV_radius_ext => k.
rewrite /PS_derive.
rewrite -plus_n_Sm plus_Sn_m /fact -/fact ?mult_INR ?S_INR.
field.
rewrite -S_INR ; split ; apply Rgt_not_eq.
by apply INR_fact_lt_0.
apply (lt_INR O), lt_O_Sn.
rewrite /l {l}.
apply PSeries_ext.
move => k ; rewrite /PS_derive.
rewrite -plus_n_Sm plus_Sn_m /fact -/fact ?mult_INR ?S_INR.
field.
rewrite -S_INR ; split ; apply Rgt_not_eq.
by apply INR_fact_lt_0.
apply (lt_INR O), lt_O_Sn.
