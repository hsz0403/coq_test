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

Lemma is_pseries_odd_even (a : nat -> R) (x l1 l2 : R) : is_pseries (fun n => a (2*n)%nat) (x^2) l1 -> is_pseries (fun n => a (2*n+1)%nat) (x^2) l2 -> is_pseries a x (l1 + x * l2).
Proof.
rewrite 3!is_pseries_R.
move => H1 H2.
apply filterlim_ext with (fun n => (sum_n (fun k : nat => a (2 * k)%nat * (x ^ 2) ^ k) (div2 n)) + x * match n with | O => 0 | S n => (sum_n (fun k : nat => a (2 * k + 1)%nat * (x ^ 2) ^ k) (div2 n)) end).
case => [ | n].
rewrite /= !sum_O /= ; ring.
case: (even_odd_dec n) => Hn.
rewrite 3!sum_n_Reals.
rewrite -(even_div2 _ Hn) {3}(even_double _ Hn).
elim: (div2 n) => {n Hn} [ | n] ; rewrite ?double_S /sum_f_R0 -/sum_f_R0.
rewrite /double /= ; ring.
rewrite -pow_mult.
replace (2 * S n)%nat with (S (S (double n))) by (rewrite -double_S /double ; ring).
replace (S (S (double n)) + 1)%nat with (S (S (S (double n)))) by ring.
move => <- ; simpl ; ring.
rewrite 3!sum_n_Reals.
rewrite -(odd_div2 _ Hn) {3}(odd_double _ Hn).
elim: (div2 n) => {n Hn} [ | n] ; rewrite ?double_S /sum_f_R0 -/sum_f_R0.
rewrite /double /= ; ring.
rewrite -?pow_mult.
replace (2 * S n)%nat with (S (S (double n))) by (rewrite -double_S /double ; ring).
replace (2 * S (S n))%nat with (S (S (S (S (double n))))) by (rewrite -double_S /double ; ring).
replace (S (S (double n)) + 1)%nat with (S (S (S (double n)))) by ring.
move => <- ; simpl ; ring.
apply (is_lim_seq_plus' _ _ l1 (x*l2)).
apply filterlim_comp with (2:=H1).
intros P [N HN].
exists (2*N+1)%nat.
intros n Hn; apply HN.
apply le_double.
apply plus_le_reg_l with 1%nat.
rewrite Plus.plus_comm.
apply le_trans with (1:=Hn).
apply le_trans with (1+double (div2 n))%nat.
case (even_or_odd n); intros J.
rewrite <- even_double; try exact J.
now apply le_S.
rewrite <- odd_double; easy.
simpl; now rewrite plus_0_r.
apply (is_lim_seq_scal_l _ x l2) => //.
apply filterlim_ext_loc with (fun n => sum_n (fun k : nat => a (2 * k + 1)%nat * (x ^ 2) ^ k) (div2 (pred n))).
exists 1%nat; intros y; case y.
easy.
intros n _; reflexivity.
apply filterlim_comp with (2:=H2).
intros P [N HN].
exists (2*N+2)%nat.
intros n Hn; apply HN.
apply le_double.
apply plus_le_reg_l with 2%nat.
rewrite Plus.plus_comm.
apply le_trans with (1:=Hn).
apply le_trans with (1+(1+double (div2 (pred n))))%nat.
case (even_or_odd (pred n)); intros J.
rewrite <- even_double; try exact J.
case n.
simpl; now apply le_S, le_S.
intros m; simpl; now apply le_S.
rewrite <- odd_double; try exact J.
case n; simpl; try easy.
now apply le_S.
simpl; now rewrite plus_0_r.
