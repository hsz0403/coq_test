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

Lemma Lim_f_p_infty : is_lim f p_infty 0.
Proof.
apply is_lim_ext_loc with (fun x => 2 / x + 2 * (ln x / x)).
exists 0.
move => y Hy.
rewrite /f /fab.
field.
by apply Rgt_not_eq.
eapply is_lim_plus.
apply is_lim_scal_l.
apply is_lim_inv.
by apply is_lim_id.
by [].
apply is_lim_scal_l.
by apply is_lim_div_ln_p.
unfold is_Rbar_plus, Rbar_plus' ; apply f_equal, f_equal ; ring.
