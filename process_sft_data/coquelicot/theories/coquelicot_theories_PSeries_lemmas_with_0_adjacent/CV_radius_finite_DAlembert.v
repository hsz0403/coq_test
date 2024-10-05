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

Lemma CV_radius_finite_DAlembert (a : nat -> R) (l : R) : (forall n:nat, a n <> 0) -> 0 < l -> is_lim_seq (fun n:nat => Rabs (a (S n) / a n)) l -> CV_radius a = Finite (/l).
Proof.
move => Ha Hl Hda.
apply Rbar_le_antisym.
rewrite /CV_radius /Lub_Rbar ; case: ex_lub_Rbar => /= cv [ub lub].
apply lub => x Hax.
case: (Rle_lt_dec x 0) => Hx.
apply Rlt_le, Rle_lt_trans with 0.
by apply Hx.
by apply Rinv_0_lt_compat.
rewrite -(Rabs_pos_eq x (Rlt_le _ _ Hx)).
rewrite -(Rmult_1_l (/l)).
replace (Rabs x) with ((Rabs x * l) /l) by (field ; apply Rgt_not_eq, Hl).
apply Rmult_le_compat_r.
by apply Rlt_le, Rinv_0_lt_compat.
apply Rnot_lt_le.
contradict Hax.
have : CV_disk a x -> is_lim_seq (fun n => a n * x ^ n) 0.
move => H.
apply ex_series_lim_0.
by apply ex_series_Rabs.
move => H H0.
move: (H H0) => {H H0}.
apply not_ex_series_DAlembert with (Rabs x * l) => //.
move => n.
apply Rmult_integral_contrapositive_currified => //.
by apply pow_nonzero, Rgt_not_eq.
apply CV_disk_DAlembert_aux.
by apply Rgt_not_eq.
by apply Ha.
by apply Hda.
apply Rbar_not_lt_le.
move : (CV_disk_outside a).
rewrite /CV_radius /Lub_Rbar ; case: ex_lub_Rbar ; case => [cv | | ] /= [ub lub] Hnot_ex H ; try by auto.
suff H0 : cv < ((cv+/l)/2) < /l.
absurd (ex_series (fun n => Rabs (a n * ((cv+/l)/2)^n))).
suff H1 : cv < Rabs ((cv + / l) / 2).
move: (Hnot_ex ((cv + / l) / 2) H1) => {Hnot_ex} Hnot_ex.
contradict Hnot_ex ; by apply ex_series_lim_0, ex_series_Rabs.
apply Rlt_le_trans with (2 := Rle_abs _), H0.
apply (CV_disk_DAlembert) with l.
by apply Ha.
by apply Hda.
right ; split.
by apply Rgt_not_eq.
rewrite Rabs_pos_eq.
by apply H0.
apply Rlt_le, Rle_lt_trans with (2 := proj1 H0).
apply ub.
exists (Rabs (a O)).
apply (is_lim_seq_ext (fun _ => Rabs (a O)) _ (Rabs (a 0%nat))).
elim => [ | n IH] /=.
by rewrite sum_O Rmult_1_r.
by rewrite sum_Sn /= Rmult_0_l Rmult_0_r Rabs_R0 /plus /= Rplus_0_r.
by apply is_lim_seq_const.
lra.
case: (ub 0) => //.
exists (Rabs (a O)).
apply (is_lim_seq_ext (fun _ => Rabs (a O)) _ (Rabs (a 0%nat))).
elim => [ | n IH] /=.
by rewrite sum_O Rmult_1_r.
by rewrite sum_Sn /= Rmult_0_l Rmult_0_r Rabs_R0 /plus /= Rplus_0_r.
by apply is_lim_seq_const.
