Require Import Reals mathcomp.ssreflect.ssreflect.
Require Import Psatz.
Require Import Rcomplements Rbar Hierarchy.
Require Import Derive RInt Continuity Lim_seq ElemFct RInt_analysis.
Ltac pos_rat := repeat ( apply Rdiv_lt_0_compat || apply Rplus_lt_0_compat || apply Rmult_lt_0_compat) ; try by apply Rlt_0_1.
Definition fab (a b x : R) : R := (a + b * ln x) / x.
Definition f (x : R) : R := fab 2 2 x.
Fixpoint u (n : nat) : R := match n with | O => 2 | S n => 2/3 * u n + 1/3 * (INR n) + 1 end.
Definition v (n : nat) : R := u n - INR n.
Definition Su (n : nat) : R := sum_f_R0 u n.
Definition Tu (n : nat) : R := Su n / (INR n) ^ 2.

Lemma Q4b : is_lim_seq Tu (1/2).
Proof.
apply is_lim_seq_ext_loc with (fun n => (6 - 4 * (2/3)^n) / (INR n ^2) + / (2 * INR n) + /2).
exists 1%nat => n Hn ; rewrite /Tu Q4a.
simpl ; field.
apply Rgt_not_eq, (lt_INR O) ; intuition.
eapply is_lim_seq_plus.
eapply is_lim_seq_plus.
eapply is_lim_seq_div.
eapply is_lim_seq_minus.
apply is_lim_seq_const.
eapply is_lim_seq_mult.
by apply is_lim_seq_const.
apply is_lim_seq_geom.
rewrite Rabs_pos_eq.
lra.
lra.
by [].
rewrite /is_Rbar_minus /is_Rbar_plus /=.
now ring_simplify (6 + - (4 * 0)).
repeat eapply is_lim_seq_mult.
apply is_lim_seq_INR.
apply is_lim_seq_INR.
apply is_lim_seq_const.
apply is_Rbar_mult_p_infty_pos.
by apply Rlt_0_1.
by [].
by [].
by apply is_Rbar_div_p_infty.
apply is_lim_seq_inv.
eapply is_lim_seq_mult.
by apply is_lim_seq_const.
by apply is_lim_seq_INR.
by apply is_Rbar_mult_sym, is_Rbar_mult_p_infty_pos, Rlt_0_2.
by [].
by [].
apply is_lim_seq_const.
apply (f_equal (@Some _)), f_equal.
field.
